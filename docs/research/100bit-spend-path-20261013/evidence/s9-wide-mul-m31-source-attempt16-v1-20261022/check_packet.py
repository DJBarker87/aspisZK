#!/usr/bin/env python3
import hashlib, json, sys
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
assert m['compiled_objects_included'] is False and m['llbc_included'] is False
for p in root.rglob('*'):
    if p.is_file():
        n=p.name.lower()
        assert not n.endswith(('.olean','.ilean','.llbc','.pyc','.so','.dylib','.dll','.exe')),(p,n)
        assert '__pycache__' not in p.parts,p
listed={x['path']:x for x in m['files']}
actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p.name not in {'manifest.json','check_packet.py','README.md'}}
assert actual==set(listed),(actual-set(listed),set(listed)-actual)
for rel,row in listed.items():
    b=(root/rel).read_bytes()
    assert hashlib.sha256(b).hexdigest()==row['sha256'],rel
    assert len(b)==row['bytes'],rel
print(f"PASS {len(listed)} source/receipt/metadata files; no LLBC/OLean/binaries")
