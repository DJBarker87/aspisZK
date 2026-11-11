"""PIN2 devnet driver library: NPC_spend.py's transaction, recording and rent helpers,
parameterised for the aspis-upload program and a new verifier, with seeded accounts.

Importing performs no I/O. init(config, out_dir) binds the run. Keys are only ever
passed by path to the devnet_spend signer; this module never reads key bytes.
Every transaction is simulated, sent, awaited to finalized, and recorded with
npc_pre/npc_post (per-transaction signed bytes, account images before/after,
CU, fee, logs), exactly as NPC_ did.
"""
import base64, hashlib, json, os, pathlib, re, subprocess, time
from r1_devnet_rpc import rpc
from r1_devnet_policy import created_accounts, state_rent
from NPC_record import npc_pre, npc_post

SYSTEM = '11111111111111111111111111111111'
TOKEN = 'TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA'
CHUNK = 3763                 # frozen upload chunk (Pin2_upload.rs CHUNK)
AFTERSTATE_BYTES = 688       # encode_pool_v1_pair_verified_afterstate_v1 prefix of proof.bin
CHECKPOINT_BYTES = 1768
C = O = None
URL = SIGNER = CLI = PAYER_KEY = None


def init(config_path, out_dir):
    global C, O, URL, SIGNER, CLI, PAYER_KEY
    C = json.load(open(config_path)); O = pathlib.Path(out_dir); O.mkdir(exist_ok=True, mode=0o700)
    URL = C['rpc_url']; SIGNER = C.get('signer', 'native-target/release/devnet_spend')
    CLI = pathlib.Path(C.get('cli_dir', str(pathlib.Path.home() / '.local/share/solana/install/active_release/bin')))
    PAYER_KEY = str(C['payer_key'])
    for k in ('upload_program',):
        assert k in C, f'config needs {k}'
    assert 'carrier' not in C, 'PIN2 runs never use the legacy carrier'
    return C


def write(name, v):
    (O / (name + '.json')).write_text(json.dumps(v, indent=2) + '\n')


def account(address, commitment='finalized'):
    return rpc(URL, 'getAccountInfo', [address, {'encoding': 'base64', 'commitment': commitment}])


def record_rent(transaction, token_authority=None):
    addresses = created_accounts(transaction)
    if not addresses:
        return
    path = O / 'rent-ledger.json'
    rows = {row['address']: row for row in json.loads(path.read_text())} if path.exists() else {}
    for address in addresses:
        value = account(address)['value']
        if value:
            rows[address] = state_rent(address, value, C['payer'], token_authority)
    write('rent-ledger', list(rows.values()))


def invoke(q):
    return json.loads(subprocess.check_output([SIGNER], input=json.dumps(q).encode()))


def plan(action, **kw):
    return invoke({**C['programs'], 'payer': C['payer'], 'upload_program': C['upload_program'], 'action': action, **kw})


def send(name, ixs, keys=None, negative=False, token_authority=None):
    """NPC_spend.send unchanged in behaviour (resume, reconcile, simulate, record)."""
    keys = keys or [PAYER_KEY]
    done = O / (name + '.json')
    if done.exists():
        old = json.load(open(done))
        if old.get('finalized'):
            if bool(old['error']) != negative:
                raise RuntimeError(f'{name}: prior finalized result had an unexpected error')
            return old
        raise RuntimeError(f'{name}: prior incomplete transaction; inspect attempt signatures before resuming')
    prior = []
    for path in O.glob(name + '-attempt-*.json'):
        if re.fullmatch(re.escape(name) + r'-attempt-[0-9]+\.json', path.name):
            prior.append((path, json.load(open(path))))
    for path, attempt_record in sorted(prior):
        sig = attempt_record['signature']
        while True:
            status = rpc(URL, 'getSignatureStatuses', [[sig], {'searchTransactionHistory': True}])['value'][0]
            if status and status['confirmationStatus'] == 'finalized':
                tx = rpc(URL, 'getTransaction', [sig, {'encoding': 'json', 'commitment': 'finalized', 'maxSupportedTransactionVersion': 1}])
                if not tx:
                    raise RuntimeError(f'{name}: finalized metadata not yet available')
                write(name + '-transaction', tx); record_rent(tx, token_authority)
                origin = attempt_record.get('started_unix', path.stat().st_mtime)
                result = {'signature': sig, 'explorer': explorer(sig), 'slot': tx['slot'],
                          'compute_units': tx['meta'].get('computeUnitsConsumed'), 'fee': tx['meta']['fee'],
                          'error': tx['meta']['err'], 'wall_seconds': time.time() - origin,
                          'wall_seconds_kind': 'reconciled_since_signed_receipt',
                          'serialized_bytes': attempt_record['serialized_bytes'], 'finalized': True,
                          'negative': negative, 'reconciled': True,
                          'note': 'reconciled after interruption: no pre/post recording for this transaction'}
                write(name, result)
                if bool(result['error']) != negative:
                    raise RuntimeError(f'{name}: reconciled unexpected result {result}')
                print(name, json.dumps(result), flush=True); return result
            if status is None and rpc(URL, 'getBlockHeight', [{'commitment': 'finalized'}]) > attempt_record['blockhash']['lastValidBlockHeight']:
                write(path.stem + '-expired', {'signature': sig, 'expired_unlanded': True}); break
            time.sleep(2)
    if not prior and list(O.glob(name + '-attempt-*.json')):
        raise RuntimeError(f'{name}: prior simulation-only failure requires inspection before resuming')
    start = time.monotonic(); started_unix = time.time()
    first_attempt = 1 + max((int(path.stem.rsplit('-', 1)[1]) for path, _ in prior), default=-1)
    for attempt in range(first_attempt, 3):
        bh = rpc(URL, 'getLatestBlockhash', [{'commitment': 'confirmed'}])['value']
        signed = invoke({'keys': keys, 'instructions': ixs, 'blockhash': bh['blockhash']})
        wire = base64.b64encode(bytes.fromhex(signed['hex'])).decode(); sig = signed['signature']
        state = npc_pre(URL, O, name, attempt, ixs, signed, C['payer'], negative)
        simulation = rpc(URL, 'simulateTransaction', [wire, {'encoding': 'base64', 'sigVerify': True, 'commitment': 'confirmed'}])
        write(f'{name}-attempt-{attempt}-simulation', simulation)
        simerr = simulation['value']['err']
        if simerr == 'BlockhashNotFound':
            continue
        if bool(simerr) != negative:
            raise RuntimeError(f'{name} unexpected simulation: {simulation}')
        write(f'{name}-attempt-{attempt}', {'signature': sig, 'blockhash': bh, 'simulation_error': simerr,
                                            'serialized_bytes': signed['bytes'], 'started_unix': started_unix})
        try:
            sent = rpc(URL, 'sendTransaction', [wire, {'encoding': 'base64', 'skipPreflight': negative, 'maxRetries': 5, 'preflightCommitment': 'confirmed'}]); assert sent == sig
        except Exception as e:
            write(f'{name}-attempt-{attempt}-send-error', {'error': str(e)})
        while True:
            status = rpc(URL, 'getSignatureStatuses', [[sig], {'searchTransactionHistory': True}])['value'][0]
            if status and status['confirmationStatus'] == 'finalized':
                break
            if not status and rpc(URL, 'getBlockHeight', [{'commitment': 'finalized'}]) > bh['lastValidBlockHeight']:
                break
            time.sleep(2)
        if not status:
            continue
        tx = None
        for _ in range(10):
            tx = rpc(URL, 'getTransaction', [sig, {'encoding': 'json', 'commitment': 'finalized', 'maxSupportedTransactionVersion': 1}])
            if tx:
                break
            time.sleep(2)
        if not tx:
            raise RuntimeError('finalized tx metadata unavailable')
        write(name + '-transaction', tx); record_rent(tx, token_authority); npc_post(URL, O, name, state, tx)
        result = {'signature': sig, 'explorer': explorer(sig), 'slot': tx['slot'],
                  'compute_units': tx['meta'].get('computeUnitsConsumed'), 'fee': tx['meta']['fee'],
                  'error': tx['meta']['err'], 'wall_seconds': time.monotonic() - start,
                  'serialized_bytes': signed['bytes'], 'finalized': True, 'negative': negative}
        write(name, result)
        if bool(result['error']) != negative:
            raise RuntimeError(f'{name} unexpected finalized result: {result}')
        print(name, json.dumps(result), flush=True); return result
    raise RuntimeError(f'{name}: blockhash expiry attempt cap reached')


def explorer(sig):
    return None if URL.startswith(('http://127.0.0.1:', 'http://localhost:')) else f'https://explorer.solana.com/tx/{sig}?cluster=devnet'


def readhex(address, owner):
    a = account(address); assert a['value'] and a['value']['owner'] == owner and not a['value']['executable']
    return base64.b64decode(a['value']['data'][0]).hex()


def create_seeded(name, entry, size):
    """CreateAccountWithSeed(base = payer, seed, owner) funded at the rent-exempt minimum."""
    existing = account(entry['address'])['value']
    if existing is not None:
        assert existing['owner'] == entry['owner'] and not existing['executable'] and len(base64.b64decode(existing['data'][0])) == size, f'{name}: unexpected existing account'
        return None
    rent = rpc(URL, 'getMinimumBalanceForRentExemption', [size])
    made = plan('pin2_create', owner=entry['owner'], seed=entry['seed'], lamports=rent, space=size)
    assert made['address'] == entry['address'], 'planner create address differs'
    return send(name, [made['instruction']])


def upload(label, entry, body):
    """Ascending-offset seeded WRITEs (one at a time), then exact readback."""
    timing_file = O / (label + '-phase-timing.json')
    if timing_file.exists():
        timing = json.load(open(timing_file))
    else:
        timing = {'started_unix': time.time(), 'origin_kind': 'phase_entry'}; write(label + '-phase-timing', timing)
    w = plan('pin2_writes', seed=entry['seed'], body=body.hex())
    assert w['address'] == entry['address'] and w['chunk'] == CHUNK and w['count'] == -(-len(body) // CHUNK)
    stats = [send(f'{label}-{i}', [ix]) for i, ix in enumerate(w['instructions'])]
    actual = bytes.fromhex(readhex(entry['address'], C['upload_program'])); assert actual == body, 'upload readback differs'
    result = {'count': len(stats), 'compute_units': sum(s['compute_units'] for s in stats),
              'wall_seconds': time.time() - timing['started_unix'], 'wall_origin_kind': timing['origin_kind'],
              'transaction_wall_seconds_sum': sum(s['wall_seconds'] for s in stats),
              'sha256': hashlib.sha256(body).hexdigest(), 'address': entry['address'], 'seed': entry['seed']}
    write(label + '-summary', result); return result


def recordings(names):
    out = []
    for n in names:
        f = O / f'{n}-recording.json'
        if f.exists():
            out.append(json.loads(f.read_text()))
    return out


def payer_delta(recs):
    d = 0
    for r in recs:
        pre = {a['key']: a for a in r['pre']['accounts']}; post = {a['key']: a for a in r['post']['accounts']}
        d += post[C['payer']]['lamports'] - pre[C['payer']]['lamports']
    return d
