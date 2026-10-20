#!/usr/bin/env python3
import hashlib, json, pathlib, sys
root=pathlib.Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]
for ent in m.get('files',[]):
    p=root/ent['path']
    if not p.is_file(): errors.append(f"missing file: {ent['path']}"); continue
    if digest(p)!=ent['sha256']: errors.append(f"hash mismatch: {ent['path']}")
    if p.stat().st_size!=ent['bytes']: errors.append(f"size mismatch: {ent['path']}")
for module in m.get('modules',[]):
    p=root/module['source']
    if not p.is_file() or digest(p)!=module['source_sha256']:
        errors.append(f"module source mismatch: {module['module']}")
    rp=root/module['receipt']
    if not rp.is_file() or digest(rp)!=module['receipt_sha256']:
        errors.append(f"receipt mismatch: {module['module']}")
if errors:
    print('\n'.join(errors)); sys.exit(1)
print(f"PASS: {len(m.get('files',[]))} packet files, {len(m.get('modules',[]))} module receipt(s)")
