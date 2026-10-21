#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
m=json.loads((R/'manifest.json').read_text()); errors=[]
if m.get('schema')!='focused-extractor-proof-packet-v1': errors.append('schema')
for rel,x in m.get('files',{}).items():
 p=R/rel
 if not p.is_file(): errors.append('missing '+rel); continue
 if p.stat().st_size!=x['bytes'] or H(p.read_bytes())!=x['sha256']: errors.append('hash/size '+rel)
for mod in m.get('modules',[]):
 p=R/mod['source']
 if not p.is_file() or H(p.read_bytes())!=mod['source_sha256']: errors.append('module source '+mod['module'])
 rec=json.loads((R/mod['receipt']).read_text())
 if H((R/mod['receipt']).read_bytes())!=mod['receipt_sha256'] or rec.get('exit_status')!=0 or rec.get('swap_bytes')!=0: errors.append('receipt '+mod['module'])
for name,x in m.get('direct_import_source_map',{}).items():
 p=R/x['source']
 if not p.is_file() or H(p.read_bytes())!=x['source_sha256']: errors.append('import source '+name)
 rec=R/'receipts'/('S3PowersToS9ScalarJoinV1.json' if name=='S3PowersToS9ScalarJoinV1' else 'S3PowersLowTotalV1.json')
 if H(rec.read_bytes())!=x['producer_receipt_sha256']: errors.append('producer receipt '+name)
if errors: print('\n'.join(errors)); sys.exit(1)
print(f"PASS: {len(m['files'])} files, {len(m['modules'])} green target, {len(m['direct_import_source_map'])} direct source owners")
