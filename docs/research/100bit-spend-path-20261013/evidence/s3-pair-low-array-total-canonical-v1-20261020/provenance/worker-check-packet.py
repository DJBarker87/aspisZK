#!/usr/bin/env python3
import hashlib, json, sys
from pathlib import Path
root = Path(__file__).resolve().parent
m = json.loads((root / 'manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
errors = []
for name, mod in m['modules'].items():
    source = root / mod['source']
    if not source.is_file() or sha(source) != mod['source_sha256']:
        errors.append(f'source hash mismatch: {name}')
    receipt = root / mod['receipt']
    if not receipt.is_file(): errors.append(f'missing receipt: {name}')
    else:
        r = json.loads(receipt.read_text())
        if r.get('exit_status') != 0: errors.append(f'nonzero receipt: {name}')
        if r.get('object_sha256') != mod['object_sha256']:
            errors.append(f'object pin mismatch: {name}')
for name, owner in m['direct_import_source_map'].items():
    source = root / owner['source_path']
    if not source.is_file() or sha(source) != owner['source_sha256']:
        errors.append(f'import source mismatch: {name}')
for e in m['evidence']:
    f = root / e['path']
    if not f.is_file() or sha(f) != e['sha256']:
        errors.append(f'evidence mismatch: {e["path"]}')
if errors:
    print('\n'.join(errors)); sys.exit(1)
print('PASS: module, import-source, receipt, and evidence hashes; no object binaries included')
