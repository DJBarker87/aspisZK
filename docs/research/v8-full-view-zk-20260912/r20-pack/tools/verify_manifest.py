#!/usr/bin/env python3
import hashlib,json,pathlib
r=pathlib.Path(__file__).resolve().parents[1];m=json.loads((r/'MANIFEST.json').read_text())
for name,rec in m['files'].items():
 p=r/name;b=p.read_bytes();assert len(b)==rec['bytes'],name
 assert hashlib.sha256(b).hexdigest()==rec['sha256'],name
print('PASS',len(m['files']),'payload hashes')
