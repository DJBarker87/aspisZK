#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys
root=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((root/'manifest.json').read_text())
errors=[]
for mod in m['modules']:
    for key in ('source','producer_receipt','command','time','log'):
        f=root/mod[key]
        if not f.is_file(): errors.append(f'missing {key}: {f}')
    src=root/mod['source']
    if src.is_file() and sha(src)!=mod['source_sha256']: errors.append('source hash mismatch')
    rec=json.loads((root/mod['producer_receipt']).read_text())
    if rec.get('source_sha256')!=mod['source_sha256']: errors.append('receipt source hash mismatch')
    if rec.get('exit_status')!=0: errors.append('nonzero accepted receipt')
for name,pin in m['direct_import_source_map'].items():
    src=(root/pin['source']).resolve()
    if not src.is_file(): errors.append(f'missing direct source {name}: {src}')
    elif sha(src)!=pin['source_sha256']: errors.append(f'direct source hash mismatch: {name}')
if errors:
    print('FAIL')
    print('\n'.join(errors))
    sys.exit(1)
print(f"PASS {m['packet']}: {len(m['modules'])} checked module(s), {len(m['direct_import_source_map'])} pinned direct source(s)")
