#!/usr/bin/env python3
import hashlib,json,pathlib,sys
root=pathlib.Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((root/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
assert m['classification'].startswith('PROVED')
assert not any(p.suffix in {'.olean','.ilean','.c','.o','.a','.so','.dylib'} for p in root.rglob('*') if p.is_file())
for rec in m['files']:
 p=root/rec['path']; assert p.is_file(),rec['path']; assert sha(p)==rec['sha256'],rec['path']
assert sha(root/m['modules'][0]['source'])==m['modules'][0]['source_sha256']
r=json.loads((root/m['modules'][0]['receipt']).read_text())
assert r['exit_status']==0 and r['source_sha256_at_launch']==r['source_sha256_after']==m['modules'][0]['source_sha256']
assert r['object_sha256']==m['modules'][0]['object_sha256']
assert r['peak_rss_bytes']>0 and r['swap_bytes']==0
post=json.loads((root/'evidence/direct-import-postflight.json').read_text())
assert post['classification'].startswith('post-run')
assert post['dependency_provenance_complete'] is False
for k,v in json.loads((root/'direct_import_source_map.json').read_text()).items():
 assert sha(root/v['source'])==v['source_sha256'],k
 assert v['selected_object_path'] and v['selected_LEAN_PATH_index']>=0,k
print('PASS',m['packet'])
