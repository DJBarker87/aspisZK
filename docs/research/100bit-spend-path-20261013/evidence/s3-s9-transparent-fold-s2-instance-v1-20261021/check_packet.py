#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
packet=Path(__file__).resolve().parent
repo=packet.parents[4]
m=json.loads((packet/'manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for row in m['modules']:
 p=packet/row['source']; assert p.is_file(),p
 assert sha(p)==row['source_sha256'],(p,sha(p),row['source_sha256'])
rec=packet/m['modules'][0]['producer_receipt']; assert rec.is_file()
r=json.loads(rec.read_text()); assert r['source_sha256']==m['modules'][0]['source_sha256']; assert r['object_sha256']==m['modules'][0]['object_sha256']; assert r['exit_status']==0
for name,row in m['direct_import_source_map'].items():
 p=packet/row['source']; assert p.is_file(),(name,p)
 assert sha(p)==row['source_sha256'],(name,sha(p),row['source_sha256'])
 pm=repo/row['producer_manifest']; assert pm.is_file(),(name,pm)
 pr=packet/row['producer_receipt']; assert pr.is_file(),(name,pr)
 assert sha(pr)==row['producer_receipt_sha256'],(name,sha(pr),row['producer_receipt_sha256'])
for rel,entry in m['files'].items():
 p=packet/rel; assert p.is_file(),p
 assert p.stat().st_size==entry['bytes'] and sha(p)==entry['sha256'],(rel,sha(p),entry)
print('source-only packet hashes PASS')
