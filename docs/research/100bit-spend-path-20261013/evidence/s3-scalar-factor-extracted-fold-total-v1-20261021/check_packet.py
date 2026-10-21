#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parent; H=lambda b:hashlib.sha256(b).hexdigest(); errors=[]
m=json.loads((R/'manifest.json').read_text())
if m.get('schema')!='focused-extractor-proof-packet-v1':errors.append('schema')
for rel,x in m.get('files',{}).items():
 p=R/rel
 if not p.is_file():errors.append('missing '+rel);continue
 if p.stat().st_size!=x['bytes'] or H(p.read_bytes())!=x['sha256']:errors.append('hash/size '+rel)
for mod in m.get('modules',[]):
 p=R/mod['source'];r=R/mod['receipt']
 if not p.is_file() or H(p.read_bytes())!=mod['source_sha256']:errors.append('module source '+mod['module'])
 if not r.is_file() or H(r.read_bytes())!=mod['receipt_sha256']:errors.append('module receipt '+mod['module'])
 elif json.loads(r.read_text()).get('exit_status')!=0:errors.append('non-green receipt '+mod['module'])
for name,x in m.get('direct_import_source_map',{}).items():
 p=R/x['source']; rr=R/'receipts'/('S3ScalarFactorTotalV1.json' if name=='S3ScalarFactorTotalV1' else 'TransparentFoldActualOpsConsumerV1.json')
 if not p.is_file() or H(p.read_bytes())!=x['source_sha256']:errors.append('import source '+name)
 if not rr.is_file() or H(rr.read_bytes())!=x['producer_receipt_sha256']:errors.append('producer receipt '+name)
if errors:print('\n'.join(errors));sys.exit(1)
print(f"PASS: {len(m['files'])} files, {len(m['modules'])} green target, {len(m['direct_import_source_map'])} direct source owners")
