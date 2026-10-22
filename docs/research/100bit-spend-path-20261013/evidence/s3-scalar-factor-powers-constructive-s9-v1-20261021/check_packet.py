#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();E=[];m=json.loads((R/'manifest.json').read_text())
if m.get('schema')!='focused-extractor-proof-packet-v1':E.append('schema')
for rel,x in m.get('files',{}).items():
 p=R/rel
 if not p.is_file():E.append('missing '+rel);continue
 if p.stat().st_size!=x['bytes'] or H(p.read_bytes())!=x['sha256']:E.append('file '+rel)
for mod in m.get('modules',[]):
 for rel,key in [(mod['source'],'source_sha256'),(mod['receipt'],'receipt_sha256')]:
  p=R/rel
  if not p.is_file() or H(p.read_bytes())!=mod[key]:E.append('module pin '+rel)
 if json.loads((R/mod['receipt']).read_text()).get('exit_status')!=0:E.append('module failed '+mod['module'])
for name,x in m.get('direct_import_source_map',{}).items():
 if not (R/x['source']).is_file() or H((R/x['source']).read_bytes())!=x['source_sha256']:E.append('import source '+name)
 if not (R/x['producer']).is_file() or H((R/x['producer']).read_bytes())!=x['producer_receipt_sha256']:E.append('import producer '+name)
if E:print('\n'.join(E));sys.exit(1)
print(f"PASS: {len(m['files'])} files, {len(m['modules'])} target, {len(m['direct_import_source_map'])} direct import owners")
