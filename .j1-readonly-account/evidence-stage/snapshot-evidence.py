#!/usr/bin/env python3
"""Read/hash-only snapshot of the completed, rejected full-SDK extraction."""
from pathlib import Path
import hashlib, json, shutil, tarfile, tomllib

W = Path('/home/dombarker/project-offloads/aspis-r1-j1a-readonly-account-20261016')
OUT = W / 'evidence-stage'
OUT.mkdir(exist_ok=False)
def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''): h.update(chunk)
    return h.hexdigest()
def put(src, rel):
    dest = OUT / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dest)
    return {'member': rel, 'source_path': str(src), 'sha256': sha(dest)}
def write(rel, value):
    dest = OUT / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(value, indent=2) + '\n')

for name in ['run-host.py', 'preflight.py', 'preflight.json', 'reservation-inventory.json',
             'tool-pins.json', 'sdk-source-pins.json', 'audit-dependencies.py',
             'audit-dependencies-initial.py', 'dependency-audit-tooling-failure.json',
             'dependency-audit.json', 'Cargo.lock.seed', 'snapshot-evidence.py']:
    put(W / name, name)
for root in ['input', 'runs', 'extraction-a']:
    for src in sorted((W / root).rglob('*')):
        if src.is_file(): put(src, str(src.relative_to(W)))

audit = json.loads((W / 'dependency-audit.json').read_text())
seed = tomllib.loads((W / 'Cargo.lock.seed').read_text())['package']
registry = Path('/home/dombarker/.cargo/registry')
index = 'index.crates.io-1949cf8c6b5b557f'
crates = {row['name'] + '-' + row['version']: row for row in audit['packages']}
for name, version in [('solana-program', '2.3.0'), ('solana-program-entrypoint', '2.3.0')]:
    lock = next(p for p in seed if p['name'] == name and p['version'] == version)
    key = name + '-' + version
    crates[key] = {**lock, 'archive': str(registry / 'cache' / index / (key + '.crate'))}
crate_pins = []
for key, row in sorted(crates.items()):
    src = Path(row['archive'])
    assert sha(src) == row['checksum'], key
    crate_pins.append({**put(src, 'registry-archives/' + src.name),
                       'name': row['name'], 'version': row['version'],
                       'checksum': row['checksum'], 'selected': key in {
                           r['name'] + '-' + r['version'] for r in audit['packages']}})
write('registry-archives.json', crate_pins)

llbc = json.loads((W / 'extraction-a/ReadonlyAccount.llbc').read_text())
t = llbc['translated']
rustsrc = Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust')
source_pins = []
for row in t['files']:
    origin = row['name']['Local']
    if origin == 'lib.rs': src = W / 'input/lib.rs'; rel = 'input/lib.rs'
    elif origin.startswith('/cargo/'):
        src = Path('/home/dombarker/.cargo') / origin.removeprefix('/cargo/')
        rel = 'source-files/registry/' + str(src.relative_to(registry / 'src' / index))
    elif origin.startswith('/rustc/'):
        src = rustsrc / origin.removeprefix('/rustc/')
        rel = 'source-files/rust/' + origin.removeprefix('/rustc/')
    else: raise AssertionError(origin)
    source_pins.append({**put(src, rel), 'llbc_file_id': row['id'], 'llbc_path': origin})
for key, path in [('solana-program-2.3.0', 'src/lib.rs'),
                  ('solana-program-2.3.0', 'src/program_error.rs'),
                  ('solana-program-2.3.0', 'Cargo.toml'),
                  ('solana-program-entrypoint-2.3.0', 'src/lib.rs')]:
    source_pins.append(put(registry / 'src' / index / key / path,
                          'source-files/registry/' + key + '/' + path))
write('source-files.json', source_pins)

def name(parts):
    return '::'.join(p['Ident'][0] if 'Ident' in p else '<impl:' + str(p['Impl']) + '>'
                    for p in parts)
decls = []
for section in ['type_decls', 'fun_decls', 'global_decls', 'trait_decls', 'trait_impls']:
    for row in t[section]:
        if row is None: continue
        meta = row['item_meta']
        shape = row.get('body', row.get('kind'))
        decls.append({'section': section, 'id': row['def_id'], 'name': name(meta['name']),
                      'raw_name': meta['name'], 'opacity': meta['opacity'],
                      'opaque': shape == 'Opaque', 'span': meta['span'],
                      'shape': next(iter(shape)) if isinstance(shape, dict) else shape})
errors = []
def walk(x, path):
    if isinstance(x, dict):
        for k, v in x.items():
            if k == 'Error': errors.append({'json_path': path + [k], 'value': v})
            walk(v, path + [k])
    elif isinstance(x, list):
        for i, v in enumerate(x): walk(v, path + [i])
walk(t, ['translated'])
account = next(x for x in t['type_decls'] if x and x['def_id'] == 0)
inventory = {'charon_version': llbc['charon_version'], 'has_errors': llbc['has_errors'],
             'llbc_sha256': sha(W / 'extraction-a/ReadonlyAccount.llbc'),
             'type_slots': len(t['type_decls']),
             'nonnull_types': sum(x is not None for x in t['type_decls']),
             'account_fields': [f['name'] for f in account['kind']['Struct']],
             'declarations': decls, 'opaque_or_foreign': [x for x in decls if
                 x['opaque'] or x['opacity'] != 'Transparent'], 'error_nodes': errors,
             'generated_files': [str(p.relative_to(W / 'extraction-a/generated'))
                 for p in (W / 'extraction-a/generated').rglob('*') if p.is_file()],
             'axiom_audit': 'NOT RUN: no Lean generated; no closure or guard theorem claimed.'}
write('llbc-inventory.json', inventory)

tools = json.loads((W / 'tool-pins.json').read_text())
runtime = []
for row in tools['tools'].values():
    src = Path(row['path']); assert sha(src) == row['sha256']; runtime.append(row['path'])
for path, digest in tools['rust_runtime_binaries'].items():
    assert sha(Path(path)) == digest; runtime.append(path)
for path, row in tools['host_dynamic_libraries'].items():
    assert sha(Path(path)) == row['sha256']; runtime.append(path)
write('final-runtime-recheck.json', {'verified_paths': runtime,
    'tool_pins_sha256': sha(W / 'tool-pins.json'), 'all_match': True})
print(json.dumps({'members_before_local_additions': sum(p.is_file() for p in OUT.rglob('*')),
                  'nonempty_type_decls': inventory['nonnull_types'],
                  'opaque_or_foreign': len(inventory['opaque_or_foreign']),
                  'error_nodes': errors, 'generated_files': inventory['generated_files']}))
