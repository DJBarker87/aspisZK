#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
p=Path(__file__).resolve().parent
m=json.loads((p/'manifest.json').read_text())
for rel,want in m['files'].items():
 got=hashlib.sha256((p/rel).read_bytes()).hexdigest()
 if got!=want: raise SystemExit(f'checksum mismatch: {rel}')
for name,row in m['direct_import_source_map'].items():
 got=hashlib.sha256((p/row['source']).read_bytes()).hexdigest()
 if got!=row['source_sha256']: raise SystemExit(f'source pin mismatch: {name}')
r=json.loads((p/'evidence/receipt.json').read_text())
if r['exit_code']!=0 or r['source_sha256']!=m['modules'][0]['source_sha256'] or r['object_sha256']!=m['modules'][0]['object_sha256']:
 raise SystemExit('compile receipt mismatch')
if 'sorryAx' in (p/'evidence/lean.log').read_text(): raise SystemExit('sorryAx audit failure')
print('PASS',len(m['files']),'files; source/object pins and standard axiom report verified')
