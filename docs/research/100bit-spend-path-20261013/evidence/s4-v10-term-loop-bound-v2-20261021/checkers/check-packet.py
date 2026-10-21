#!/usr/bin/env python3
import hashlib, json, pathlib
base = pathlib.Path(__file__).resolve().parents[1]
repo = pathlib.Path(__file__).resolve().parents[6]
m = json.loads((base / 'manifest.json').read_text())
for mod in m['modules']:
    p = base / mod['source']
    assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest() == mod['source_sha256'], mod['name']
    assert mod['exit_status'] == 0 and mod['swap_bytes'] == 0, mod['name']
for name, owner in m['direct_import_source_map'].items():
    p = repo / owner['source']
    assert p.is_file(), (name, p)
    assert hashlib.sha256(p.read_bytes()).hexdigest() == owner['source_sha256'], name
for p in base.rglob('*'):
    if p.is_file() and p.suffix in {'.olean', '.ilean', '.so', '.dylib', '.a', '.rlib'}:
        raise SystemExit(f'compiled artifact included: {p}')
print('PASS: packet source and direct import source pins; no compiled artifacts')
