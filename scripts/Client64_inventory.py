"""Read-only inventory of configured retained roots; never returns private JSON."""
import base64
import hashlib
import json
import os
from pathlib import Path
import stat
from Client64_proof_accounts import validate_keys, validate_plan

ALPHABET = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'


def b58(data):
    n = int.from_bytes(data, 'big'); out = ''
    while n:
        n, r = divmod(n, 58); out = ALPHABET[r] + out
    return '1' * (len(data)-len(data.lstrip(b'\0'))) + out


def checked(path, mode=None, directory=False):
    path = Path(path).absolute()
    for parent in [*reversed(path.parents), path]:
        if parent.is_symlink():
            raise ValueError('symlink')
    info = path.stat()
    if not (stat.S_ISDIR(info.st_mode) if directory else stat.S_ISREG(info.st_mode)):
        raise ValueError('wrong file type')
    actual = stat.S_IMODE(info.st_mode)
    if mode is not None and actual != mode:
        raise ValueError('unsafe mode')
    if not info.st_mode & 0o400 or not os.access(path, os.R_OK):
        raise ValueError('unreadable')
    return oct(actual)


def load(path, private=False):
    checked(path, 0o600 if private else None)
    try:
        return json.loads(Path(path).read_text())
    except Exception:
        raise ValueError('unreadable or malformed JSON') from None


def walk(root):
    checked(root, directory=True)
    def required_io_error(error):
        raise error
    for base, dirs, files in os.walk(root, followlinks=False, onerror=required_io_error):
        for name in sorted(dirs + files):
            p = Path(base)/name
            if p.is_symlink():
                raise ValueError('symlink at ' + str(p))
        checked(base, directory=True)
        for name in sorted(files):
            yield Path(base)/name


def discover(config, public):
    """public(path) reads a public identifier only; errors never include its output."""
    errors = []; keys = {}; recovery = {}; extra = set(); setups = []
    def error(path, reason):
        errors.append({'path': str(path), 'error': reason})
    def guard(path, fn):
        try:
            return fn()
        except Exception:
            error(path, 'missing, unreadable, malformed, symlink, unsafe mode or inconsistent data')
    def key(p):
        p = p.absolute()
        if str(p) in keys: return keys[str(p)]['pubkey']
        mode = checked(p, 0o600)
        try: address = public(p)
        except Exception: raise ValueError('public-key reader failed') from None
        if not isinstance(address, str) or not 32 <= len(address) <= 44:
            raise ValueError('invalid public identifier')
        n = 0
        for char in address:
            n = n * 58 + ALPHABET.index(char)
        raw = bytes(len(address)-len(address.lstrip('1'))) + n.to_bytes((n.bit_length()+7)//8, 'big')
        if len(raw) != 32 or not any(raw) or b58(raw) != address:
            raise ValueError('invalid public identifier')
        keys[str(p)] = dict(path=str(p), pubkey=address, mode=mode, retained=True)
        return address
    def recover(p):
        mode = checked(p, 0o600)
        if not isinstance(load(p, True), dict): raise ValueError('recovery JSON object required')
        recovery[str(p.absolute())] = dict(path=str(p.absolute()), mode=mode, retained=True)
    def roots(name, defaults):
        values = config.get(name, [])
        if not isinstance(values, list) or not all(isinstance(v, str) for v in values):
            raise ValueError('inventory roots must be path lists')
        return sorted(set(Path(v).absolute() for v in [*defaults, *values]))
    key_roots = roots('inventory_key_roots', ['keys'])
    artifact_roots = roots('inventory_artifact_roots', ['artifacts'])
    repeat_roots = []
    def find_repeat_roots():
        # Path.glob can suppress listing errors; discovery must fail closed.
        with os.scandir('receipts') as entries:
            for entry in entries:
                if entry.name.startswith('spend'):
                    repeat_roots.append(str(Path('receipts')/entry.name))
    guard('receipts', find_repeat_roots)
    spend_roots = roots('inventory_spend_roots', ['receipts/spend', *repeat_roots])
    for root in key_roots + artifact_roots:
        def scan(root=root):
            for p in walk(root):
                if (root in key_roots and p.parent == root and p.suffix == '.json') or p.name.endswith('-keypair.json'):
                    guard(p, lambda p=p: key(p))
        guard(root, scan)
    for root in spend_roots:
        def scan_spend(root=root):
            all_files = []
            # Keep files yielded before a listing error and continue routine
            # manifest/setup discovery, while the guard prevents completion/RPC.
            guard(root, lambda: all_files.extend(walk(root)))
            private_dirs = [p for p in root.iterdir() if p.name.endswith('-proof-private')]
            for private in private_dirs:
                def scan_private(private=private):
                    checked(private, 0o700, directory=True)
                    files = [p for p in all_files if private in p.parents]
                    for directory in {p.parent for p in files}:
                        checked(directory, 0o700 if directory in (private, private/'proof') else None, directory=True)
                        if directory.stat().st_mode & 0o022:
                            raise ValueError('writable private child directory')
                    for p in files:
                        # Validate every retained private file, including staging metadata.
                        guard(p, lambda p=p: checked(p, None if p.name in ('proof.bin', 'statement.bin') else 0o600))
                        if p.name.startswith('attempt-'):
                            guard(p, lambda p=p: key(p))
                        if p.name.startswith('manifest.json.staging-'):
                            guard(p, lambda p=p: load(p, True))
                        if p.name == 'note-recovery.json':
                            guard(p, lambda p=p: recover(p))
                    if 'client64' not in private.name: return
                    manifest = private/'manifest.json'
                    state = load(manifest, True)
                    if not isinstance(state, dict): raise ValueError('manifest object required')
                    if state.get('state') not in ('ready', 'entered', 'failed', 'success'):
                        raise ValueError('incomplete allocation')
                    entries = state['keys']
                    validate_keys([e['public'] for e in entries])
                    for i, entry in enumerate(entries):
                        expected = private/f'attempt-{i}.json'
                        if entry['path'] != str(expected) or key(expected) != entry['public']:
                            raise ValueError('manifest key mismatch')
                    if state['state'] != 'success':
                        error(manifest, 'incomplete proof run: ' + state['state'])
                    else:
                        plan = state['plan']; identity = state['identity']
                        validate_plan(plan, [e['public'] for e in entries], identity)
                        request = state['request']
                        if (request['proof_accounts'] != [e['public'] for e in entries] or
                                request['proof_dir'] != str(private/'proof') or
                                any(request.get(k) != v for k, v in identity.items())):
                            raise ValueError('request mapping mismatch')
                        for name, digest in state['artifacts'].items():
                            if name not in ('proof.bin', 'statement.bin'): raise ValueError('unexpected artifact')
                            p = private/'proof'/name; checked(p)
                            if hashlib.sha256(p.read_bytes()).hexdigest() != digest: raise ValueError('artifact mismatch')
                        if set(state['artifacts']) != {'proof.bin', 'statement.bin'}: raise ValueError('missing artifacts')
                        recover(private/'proof/note-recovery.json')
                        extra.add(plan['marker'])
                        exported = root/(private.name.removesuffix('-client64-proof-private')+'-proof-plan.json')
                        if exported.exists() and load(exported) != plan:
                            raise ValueError('exported plan mismatch')
                guard(private, scan_private)
            setup = load(root/'setup-plan.json')
            setups.append(setup)
            extra.update([setup[k] for k in ('vault','vault_authority','master','registry_account','entry')])
            extra.update(setup['lanes'])
            for op in ('transfer', 'withdrawal'):
                plan_path = root/f'{op}-proof-plan.json'
                if plan_path.exists():
                    plan = load(plan_path); extra.add(plan['marker'])
                    if plan.get('client_route') == 'selected64-proof-account-v1':
                        if not (root/f'{op}-client64-proof-private').is_dir():
                            raise ValueError('missing selected mapping')
                    else:
                        recover(root/f'{op}-proof-private/note-recovery.json')
                elif not (root/f'{op}-client64-proof-private').exists():
                    error(plan_path, 'missing proof plan and retained mapping')
        guard(root, scan_spend)
    return dict(keys=list(keys.values()), note_recovery_files=list(recovery.values()), errors=errors,
                configured_roots=dict(keys=list(map(str,key_roots)), artifacts=list(map(str,artifact_roots)),
                                      spend=list(map(str,spend_roots)))), extra, setups


def build_report(config, public, rpc):
    result, extra, setups = discover(config, public)
    result.update(scope='Configured/known retained roots only; not all possible wallets. No cleanup or refund.',
                  complete=False, retained_refund_destination=config['payer'], refund_signatures=[])
    result['key_directory_mode'] = checked('keys', directory=True)
    result['accounts'] = {}; result['programs'] = {}; result['context_slots'] = []
    if result['errors']: return result
    addresses = sorted({k['pubkey'] for k in result['keys']} | extra | {config['payer']})
    for offset in range(0, len(addresses), 100):
        batch = addresses[offset:offset+100]
        r = rpc(config['rpc_url'], 'getMultipleAccounts', [batch, {'commitment':'finalized','encoding':'base64'}])
        if len(r['value']) != len(batch): raise ValueError('incomplete account response')
        result['context_slots'].append(r['context']['slot'])
        for address, a in zip(batch, r['value']):
            if a is None: result['accounts'][address] = {'exists':False,'lamports':0}; continue
            data = base64.b64decode(a['data'][0], validate=True)
            v = dict(exists=True, lamports=a['lamports'], owner=a['owner'], executable=a['executable'],
                     data_bytes=len(data), data_sha256=hashlib.sha256(data).hexdigest())
            if a['owner'] == 'TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA':
                if len(data)==165: v['token']=dict(mint=b58(data[:32]),authority=b58(data[32:64]),amount_base_units=int.from_bytes(data[64:72],'little'))
                if len(data)==82: v['mint']=dict(authority=b58(data[4:36]) if int.from_bytes(data[:4],'little')==1 else None,supply_base_units=int.from_bytes(data[36:44],'little'),decimals=data[44],freeze_authority=b58(data[50:82]) if int.from_bytes(data[46:50],'little')==1 else None)
            result['accounts'][address] = v
    for role in ('verifier','pool','registry','carrier'):
        meta=load(Path('receipts/deploy-fresh')/(role+'-programdata.json'))
        a=rpc(config['rpc_url'],'getAccountInfo',[meta['address'],{'commitment':'finalized','encoding':'base64'}])
        v=a['value']; data=base64.b64decode(v['data'][0], validate=True)
        if v['owner']!='BPFLoaderUpgradeab1e11111111111111111111111' or v['executable'] or len(data)<45 or int.from_bytes(data[:4],'little')!=3: raise ValueError('invalid programdata')
        h=hashlib.sha256(data[45:]).hexdigest()
        authority=b58(data[13:45]) if data[12] else None
        if h!=config['release_artifacts']['devnet_verifier' if role=='verifier' else role]['sha256'] or authority!=(None if role in ('verifier','registry') else config['payer']): raise ValueError('program pin/authority mismatch')
        result['programs'][role]=dict(programdata=meta['address'],lamports=v['lamports'],last_deploy_slot=int.from_bytes(data[4:12],'little'),upgrade_authority=authority,elf_sha256=h,readback_context_slot=a['context']['slot'])
    result['complete']=True
    return result
