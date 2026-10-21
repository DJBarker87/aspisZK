#!/usr/bin/env python3
import hashlib, json, pathlib, subprocess, sys
repo = pathlib.Path(__file__).resolve().parents[6]
base = pathlib.Path(__file__).resolve().parents[1]
m = json.loads((base/'manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for mod in m['modules']:
    p=base/mod['source']
    if not p.is_file() or sha(p)!=mod['source_sha256']:
        raise SystemExit(f"module source mismatch: {mod['name']}")
    if mod['exit_status']!=0 or mod['swap_bytes']!=0:
        raise SystemExit(f"module receipt not green/zero-swap: {mod['name']}")
for name, owner in m['direct_import_source_map'].items():
    rel=owner.get('source','')
    if rel.startswith('not retained') or rel.startswith('upstream package'):
        continue
    p=repo/rel
    if not p.is_file() or sha(p)!=owner['source_sha256']:
        raise SystemExit(f"source owner mismatch: {name}: {p}")
for p in base.rglob('*'):
    if p.is_file() and p.suffix in {'.olean','.ilean','.so','.dylib','.a','.rlib'}:
        raise SystemExit(f"compiled artifact is included: {p}")
subprocess.run([sys.executable,str(base/'checkers/check-generated-body-cut.py')],check=True)
print('PASS: manifest sources/import source pins, green receipt fields, no compiled artifacts, and exact emitted-body cut')
