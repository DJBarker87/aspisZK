"""Selected64 retained account lifecycle. Importing this module performs no I/O.

No automatic proof retry after invocation failure or ambiguous interruption.
All generated keys, including staging files, are retained for manual recovery.
"""
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import time

ROUTE = 'selected64-proof-account-v1'
CAP = 8
ALPHABET = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'


def validate_keys(keys):
    if not isinstance(keys, list) or len(keys) != CAP:
        raise ValueError('proof_accounts requires eight retained public keys')
    for key in keys:
        if not isinstance(key, str) or not 32 <= len(key) <= 44 or any(c not in ALPHABET for c in key):
            raise ValueError('malformed proof account')
        number = 0
        for c in key:
            number = number * 58 + ALPHABET.index(c)
        raw = b'\0' * (len(key) - len(key.lstrip('1'))) + number.to_bytes((number.bit_length()+7)//8, 'big')
        if len(raw) != 32 or not any(raw):
            raise ValueError('proof account must be nonzero 32 bytes')
    if len(set(keys)) != CAP:
        raise ValueError('duplicate proof account')
    return keys


def sync_dir(path):
    fd = os.open(path, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def private_file(path):
    info = path.lstat()
    if not stat.S_ISREG(info.st_mode) or stat.S_IMODE(info.st_mode) != 0o600:
        raise ValueError('private file must be regular and mode 0600')


def atomic_json(path, value):
    # Retain a staging copy on every failure. Only manifest metadata is replaced.
    stage = path.with_name(path.name + f'.staging-{os.getpid()}-{time.monotonic_ns()}')
    fd = os.open(stage, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, 'w') as stream:
        json.dump(value, stream, sort_keys=True, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(stage, path)
    sync_dir(path.parent)


def retain_key(path, cli):
    """Only called by the actual script; tests inject public-only mocks."""
    stage = path.with_name(path.name + '.generated-private')
    # Parent is private and newly allocated. Refuse any prior partial generation.
    if path.exists() or stage.exists():
        raise ValueError('retained key allocation already exists; manual recovery required')
    old_umask = os.umask(0o077)
    try:
        subprocess.run([str(cli/'solana-keygen'), 'new', '--no-bip39-passphrase',
                        '--silent', '-o', str(stage)], stdout=subprocess.DEVNULL, check=True)
    finally:
        os.umask(old_umask)
    os.chmod(stage, 0o600)
    private_file(stage)
    with stage.open('rb') as stream:
        os.fsync(stream.fileno())
    os.link(stage, path)  # exclusive publication; never replace a legacy key
    sync_dir(path.parent)
    return key_public(path, cli)


def key_public(path, cli):
    private_file(path)
    return subprocess.check_output([str(cli/'solana-keygen'), 'pubkey', str(path)], text=True).strip()


def validate_plan(plan, keys, identity):
    validate_keys(keys)
    attempts, index = plan.get('attempts'), plan.get('attempt_index')
    if (type(attempts) is not int or type(index) is not int or
            not 1 <= attempts <= CAP or index != attempts - 1 or
            plan.get('client_route') != ROUTE or plan.get('proof_account') != keys[index]):
        raise ValueError('planner selected account/attempt mismatch')
    # Exact roles from the unchanged transaction interfaces, including flags.
    stage, settle = plan['stage1'], plan['settle']
    if (stage['program'] != identity['verifier'] or settle['program'] != identity['pool'] or
            stage['accounts'] != [[keys[index], False, False],
                                  [identity['public_account'], False, False],
                                  [identity['verifier_checkpoint'], False, True]] or
            settle['accounts'][10] != [keys[index], False, False] or
            settle['accounts'][-1] != [identity['verifier_checkpoint'], False, False] or
            settle['accounts'][1] != [identity['checkpoint'], False, False]):
        raise ValueError('planner instruction account mismatch')
    return index


def artifact_hashes(proof_dir):
    return {name: hashlib.sha256((proof_dir/name).read_bytes()).hexdigest()
            for name in ('proof.bin', 'statement.bin')}


def proof_plan(root, identity, prepare, invoke, absent, generate, public, legacy_plan=None):
    """Return (validated plan, retained selected path), without funding anything.

    prepare supplies live snapshots only for a fresh invocation. identity contains
    all stable request fields; the manifest retains the complete original request.
    absent/public/generate/invoke are production wiring or offline test doubles.
    """
    root = Path(root).absolute()
    manifest = root/'manifest.json'
    if not root.exists():
        if legacy_plan is not None and Path(legacy_plan).exists():
            raise ValueError('legacy proof plan has no selected64 mapping; retain for recovery')
        root.mkdir(mode=0o700)
        sync_dir(root.parent)
        atomic_json(manifest, {'state': 'allocating', 'identity': identity})
        entries = []
        for i in range(CAP):
            path = root/f'attempt-{i}.json'
            entries.append({'path': str(path), 'public': generate(path)})
        keys = validate_keys([entry['public'] for entry in entries])
        state = {'state': 'ready', 'identity': identity, 'keys': entries}
        atomic_json(manifest, state)
    info = root.lstat()
    if not stat.S_ISDIR(info.st_mode) or stat.S_IMODE(info.st_mode) != 0o700:
        raise ValueError('selected64 directory must be private mode 0700')
    private_file(manifest)
    state = json.loads(manifest.read_text())
    if state.get('identity') != identity or state.get('state') not in ('ready', 'success'):
        raise ValueError('failed/incomplete proof mapping; retain keys and inspect manually')
    entries = state['keys']
    keys = validate_keys([entry['public'] for entry in entries])
    for i, entry in enumerate(entries):
        expected = root/f'attempt-{i}.json'
        if entry['path'] != str(expected) or public(expected) != keys[i]:
            raise ValueError('retained key mapping changed')
    proof_dir = root/'proof'
    if state['state'] == 'success':
        request = state['request']
        if (request.get('proof_accounts') != keys or request.get('proof_dir') != str(proof_dir) or
                any(request.get(k) != v for k, v in identity.items())):
            raise ValueError('persisted request mapping changed')
        plan = state['plan']
        index = validate_plan(plan, keys, identity)
        if artifact_hashes(proof_dir) != state['artifacts']:
            raise ValueError('retained proof artifacts changed')
        if legacy_plan is not None and Path(legacy_plan).exists():
            if json.loads(Path(legacy_plan).read_text()) != plan:
                raise ValueError('exported proof plan differs from private success mapping')
        return plan, entries[index]['path']
    # A permanent exclusive claim protects concurrent launch and ambiguous crash.
    claim = root/'invocation-claimed'
    fd = os.open(claim, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    os.fsync(fd)
    os.close(fd)
    sync_dir(root)
    try:
        for key in keys:
            if not absent(key):
                raise ValueError('proof account already exists; cannot treat as fresh')
        request = {**identity, **prepare(), 'proof_accounts': keys, 'proof_dir': str(proof_dir)}
        # prepare is a snapshot supplier, never allowed to change stable identities.
        if any(request.get(k) != v for k, v in identity.items()):
            raise ValueError('snapshot changed request identity')
        state.update(state='entered', request=request)
        atomic_json(manifest, state)
        plan = invoke(request)
        index = validate_plan(plan, keys, identity)
        state.update(state='success', plan=plan, artifacts=artifact_hashes(proof_dir))
        atomic_json(manifest, state)
        return plan, entries[index]['path']
    except BaseException:
        # Never reset the store or regenerate keys, even if this write also fails.
        state['state'] = 'failed'
        atomic_json(manifest, state)
        raise
