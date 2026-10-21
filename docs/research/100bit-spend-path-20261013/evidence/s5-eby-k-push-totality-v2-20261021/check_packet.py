#!/usr/bin/env python3
import hashlib,json,sys
from pathlib import Path
p=Path(__file__).resolve().parent
m=json.loads((p/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
assert m['packet']=='s5-eby-k-push-totality-v2-20261021'
for item in m['files']:
 f=p/item['path']; assert f.is_file(),item['path']
 assert hashlib.sha256(f.read_bytes()).hexdigest()==item['sha256'],item['path']
 assert f.stat().st_size==item['size_bytes'],item['path']
for name,pin in m['direct_import_source_map'].items():
 f=p/pin['repository_path']; assert f.is_file(),(name,str(f))
 assert hashlib.sha256(f.read_bytes()).hexdigest()==pin['source_sha256'],name
assert not list(p.rglob('*.olean'))
assert not list(p.rglob('*.ilean'))
rec=json.loads((p/m['modules'][0]['receipt']).read_text())
assert rec['exit_status']==0 and rec['source_sha256']==rec['source_sha256_after']
assert rec['source_sha256']==m['modules'][0]['source_sha256']
log=(p/'evidence/lean.log').read_text()
assert 'push_success_product_update_of_valid_scalar' in log
assert 'sorryAx' not in log
for ax in ('propext','Classical.choice','Quot.sound'):
 assert ax in log
assert 'native_decide' not in (p/'sources/EbyKPushTotalityV1.lean').read_text()
print('PASS',len(m['files']),'files',len(m['direct_import_source_map']),'direct imports')
