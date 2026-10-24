import json,hashlib
from pathlib import Path
p=Path(__file__).resolve().parent
r=p.parents[4]
x=json.loads((p/'application.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
review=p.parent/'s9-h5-adoption-review-20261023'
s=json.loads((review/'source-pins.json').read_text())
assert x['applied'] and not x['deployment_performed']
assert x['owner_approved_cu_delta']==12214
assert x['security_target_status']=='not yet established'
assert sha(review/s['final_patch'])==x['patch_sha256']
for name,v in x['sources'].items():
 assert sha(r/name)==v['candidate_sha256'],name
 assert sha(review/v['candidate_file'])==v['candidate_sha256'],name
u=x['unchanged_caller'];assert sha(r/u['path'])==u['sha256']
print('PASS: four applied candidate hashes and unchanged caller; source/cone/security obligations remain explicit')
