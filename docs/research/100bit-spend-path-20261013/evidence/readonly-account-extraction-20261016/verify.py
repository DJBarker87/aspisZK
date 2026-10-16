#!/usr/bin/env python3
"""Verify retained source/dependency/failure evidence; runs no compiler or prover."""
from pathlib import Path
import hashlib
import io
import json
import subprocess
import tarfile
import tomllib

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parents[1]
REV = 'b2ad6649de4c1b97c2270a1c8bd4bbfe5537d52c'
LIMITS = {'memory.high': '6442450944', 'memory.max': '8589934592', 'memory.swap.max': '0'}
def sha(data): return hashlib.sha256(data).hexdigest()
def load(data): return json.loads(data)

pin = load((HERE / 'archive-pin.json').read_bytes())
archive = HERE / 'readonly-account-evidence.tar.gz'
assert len(archive.read_bytes()) == pin['bytes'] and sha(archive.read_bytes()) == pin['sha256']
members = load((HERE / 'archive-members.json').read_bytes())
with tarfile.open(archive) as tar:
    actual = tar.getmembers()
    assert len(actual) == len(members) == pin['members']
    assert len({m.name for m in actual}) == len(actual)
    assert all(m.isfile() and not Path(m.name).is_absolute() and
               '..' not in Path(m.name).parts and m.name in members for m in actual)
    def read(name): return tar.extractfile(name).read()
    def js(name): return load(read(name))
    for name, expected in members.items():
        data = read(name)
        assert len(data) == expected['bytes'] and sha(data) == expected['sha256'], name

    sourcepins = js('input/source-pins.json')
    assert sourcepins['source_revision'] == REV
    original = subprocess.check_output(['git', 'show', REV + ':' + sourcepins['source']], cwd=RESEARCH)
    assert original == read('source-files/project/r1_pool_adapter.rs')
    assert sha(original) == sourcepins['source_sha256']
    first, last = sourcepins['span']
    exact = b''.join(original.splitlines(keepends=True)[first-1:last])
    assert exact.decode() == sourcepins['exact_declaration'] and sha(exact) == sourcepins['span_sha256']
    kit = RESEARCH / 'tools/readonly-account-extraction-kit'
    for name in [*sourcepins['kit_files'], 'source-pins.json', 'Cargo.lock']:
        assert read('input/' + name) == (kit / name).read_bytes(), name
    for name, digest in sourcepins['kit_files'].items():
        assert sha(read('input/' + name)) == digest
    seed_bytes = subprocess.check_output(['git', 'show', REV + ':Cargo.lock'], cwd=RESEARCH)
    assert seed_bytes == read('Cargo.lock.seed')
    assert sha(seed_bytes) == sourcepins['seed_lock_sha256']

    original_lock = tomllib.loads(seed_bytes.decode())['package']
    selected = tomllib.loads(read('input/Cargo.lock').decode())['package']
    old = {(r['name'], r['version'], r.get('source')): r for r in original_lock}
    selected_registry = [r for r in selected if r.get('source')]
    # Cargo.lock also retains packages for other targets; metadata was filtered
    # to x86_64-unknown-linux-gnu for this actual attempt.
    assert len(selected_registry) == 91
    for row in selected_registry:
        assert old[(row['name'], row['version'], row['source'])]['checksum'] == row['checksum']
    dep = js('dependency-audit.json')
    assert dep['source_revision'] == REV and dep['all_selected_versions_and_checksums_equal_seed']
    assert dep['selected_lock_sha256'] == sha(read('input/Cargo.lock'))
    assert dep['seed_lock_sha256'] == sha(seed_bytes)
    assert dep['metadata_sha256'] == sha(read('runs/metadata-a/stdout.log'))
    assert len(dep['packages']) == 65
    for row in dep['packages']:
        assert next(r for r in selected_registry if
                    (r['name'], r['version']) == (row['name'], row['version']))['checksum'] == row['checksum']
    assert dep['sdk_features'] == {
        'solana-account-info': ['bincode'], 'solana-program-error': ['borsh', 'serde'],
        'solana-pubkey': ['borsh', 'bytemuck', 'curve25519', 'serde', 'sha2', 'std']}
    crates = {(r['name'], r['version']): r for r in js('registry-archives.json')}
    assert len(crates) == 67 and sum(r['selected'] for r in crates.values()) == 65
    for key, row in crates.items():
        assert sha(read(row['member'])) == row['checksum'] == row['sha256']
        assert next(r for r in original_lock if (r['name'], r['version']) == key)['checksum'] == row['checksum']
    source_files = js('registry-source-file-audit.json')
    count = 0
    assert len(source_files) == 65
    for row in source_files:
        cr = crates[(row['name'], row['version'])]
        assert cr['selected'] and cr['checksum'] == row['archive_sha256']
        with tarfile.open(fileobj=io.BytesIO(read(cr['member']))) as ct:
            found = {}
            prefix = row['name'] + '-' + row['version']
            for m in ct.getmembers():
                if not m.isfile(): continue
                rel = str(Path(m.name).relative_to(prefix)); data = ct.extractfile(m).read()
                found[rel] = {'bytes': len(data), 'sha256': sha(data)}
            assert found == row['files']
            count += len(found)
    assert count == dep['verified_source_files'] == 1873
    for row in js('source-files.json'):
        data = read(row['member']); assert sha(data) == row['sha256']
        if row['member'].startswith('source-files/registry/'):
            rel = Path(row['member']).relative_to('source-files/registry')
            cr = next(r for r in crates.values() if r['name'] + '-' + r['version'] == rel.parts[0])
            with tarfile.open(fileobj=io.BytesIO(read(cr['member']))) as ct:
                assert ct.extractfile(str(rel)).read() == data

    llbc = js('extraction-a/ReadonlyAccount.llbc'); t = llbc['translated']
    inventory = js('llbc-inventory.json')
    assert inventory['llbc_sha256'] == sha(read('extraction-a/ReadonlyAccount.llbc'))
    assert llbc['has_errors'] is False and llbc['charon_version'] == '0.1.223'
    assert len(t['type_decls']) == 14 and sum(r is not None for r in t['type_decls']) == 13
    assert len(t['fun_decls']) == 11
    assert t['fun_decls'][0]['item_meta']['source_text'] == exact.decode().rstrip('\n')
    assert 'Structured' in t['fun_decls'][0]['body']
    account = t['type_decls'][0]
    assert account['item_meta']['opacity'] == 'Transparent'
    assert [r['name'] for r in account['kind']['Struct']] == inventory['account_fields'] == [
        'key', 'lamports', 'data', 'owner', 'rent_epoch', 'is_signer', 'is_writable', 'executable']
    def display(parts):
        return '::'.join(p['Ident'][0] if 'Ident' in p else '<impl:' + str(p['Impl']) + '>' for p in parts)
    decls = []
    for section in ['type_decls', 'fun_decls', 'global_decls', 'trait_decls', 'trait_impls']:
        for row in t[section]:
            if row is None: continue
            m = row['item_meta']; shape = row.get('body', row.get('kind'))
            decls.append({'section': section, 'id': row['def_id'], 'name': display(m['name']),
                          'raw_name': m['name'], 'opacity': m['opacity'], 'opaque': shape == 'Opaque',
                          'span': m['span'], 'shape': next(iter(shape)) if isinstance(shape, dict) else shape})
    assert decls == inventory['declarations']
    foreign = [r for r in decls if r['opaque'] or r['opacity'] != 'Transparent']
    assert foreign == inventory['opaque_or_foreign'] and len(foreign) == 18
    assert sum(r['opaque'] for r in decls) == 9
    errors = []
    def walk(value, path):
        if isinstance(value, dict):
            for key, x in value.items():
                if key == 'Error': errors.append({'json_path': path + [key], 'value': x})
                walk(x, path + [key])
        elif isinstance(value, list):
            for i, x in enumerate(value): walk(x, path + [i])
    walk(t, ['translated'])
    assert errors == inventory['error_nodes'] and len(errors) == 1
    assert errors[0]['value'] == 'removed allocator parameter'
    assert inventory['generated_files'] == []
    assert not any(n.startswith('extraction-a/generated/') for n in members)
    for label, status in [('metadata-a', 0), ('charon-a', 0), ('aeneas-a', 2)]:
        row = js('runs/' + label + '/receipt.json')
        assert row['exit_status'] == status and row['source_revision'] == REV
        assert row['limits'] == LIMITS and row['swaps'] == 0
        assert row['timeout_seconds'] == 180 and row['wall_seconds'] < 180
        assert row['runner_sha256'] == sha(read('run-host.py'))
        assert 'oom 0\n' in row['memory_events'] and 'oom_kill 0\n' in row['memory_events']
    charon = js('runs/charon-a/receipt.json')['command']
    assert ['--start-from', 'crate::r1_pool_adapter::require_readonly_account'] == charon[
        charon.index('--start-from'):charon.index('--start-from')+2]
    assert all(x in charon for x in ['--locked', '--offline', '--release', '--lib'])
    failure = read('runs/aeneas-a/stdout.log').decode()
    for text in ['unsupported type:', 'TPattern', 'TRawPtr', 'NotNull',
                 'core/src/ptr/non_null.rs', 'TypesAnalysis.ml, line 486']:
        assert text in failure, text
    toolpins = js('tool-pins.json')
    retained = load((HERE.parent / 'native-r18-tools-20261016/tools-final-pins.json').read_bytes())
    for key in toolpins: assert toolpins[key] == retained[key], key
    assert js('final-runtime-recheck.json')['all_match']
    assert js('final-runtime-recheck.json')['tool_pins_sha256'] == sha(read('tool-pins.json'))
    reservation = js('reservation-inventory.json')
    assert reservation['sum_memorymax_upper_bound'] == 16 * 2**30 < reservation['safe_limit']
    assert sha(read('source-files/aeneas/TypesAnalysis.ml')) == js('aeneas-source-pin.json')['sha256']
    native = HERE.parent / 'native-r18-tools-20261016'
    native_tar = (native / 'native-tools-evidence.tar.gz').read_bytes()
    assert sha(native_tar) == load((native / 'bundle-manifest.json').read_bytes())['native-tools-evidence.tar.gz']
    with tarfile.open(fileobj=io.BytesIO(native_tar)) as nt:
        source_archive = nt.extractfile('inputs/aeneas-exact-source.tar.gz').read()
        assert sha(source_archive) == js('aeneas-source-pin.json')['archive_sha256']
        assert sha(source_archive) == toolpins['source_archives']['aeneas']['archive_sha256']
        with tarfile.open(fileobj=io.BytesIO(source_archive)) as st:
            assert st.extractfile(js('aeneas-source-pin.json')['archive_member']).read() == read(
                'source-files/aeneas/TypesAnalysis.ml')
    assert read('REPORT.txt') == (RESEARCH / 'design/J1-READONLY-ACCOUNT-EXTRACTION-20261016.txt').read_bytes()
    assert len(read('REPORT.txt').decode().split()) < 800
    assert js('check-summary.json') == load((HERE / 'check-summary.json').read_bytes())
print(f'PASS: {len(members)} members; exact unchanged helper; 67 crate archives/1873 audited '
      'source files; full SDK LLBC; 18 opaque/foreign entries and one Error marker; '
      'Charon 0/Aeneas 2 under 6G/8G/swap0; no generated Lean or theorem claim.')
