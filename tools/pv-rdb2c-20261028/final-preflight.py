from pathlib import Path
import json,hashlib,lzma,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');env=json.loads((D/'env-J.json').read_text());roots=list(map(Path,env['LEAN_PATH'].split(':')))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
for r in json.loads((D/'external.json').read_text()):
 rel=r['module']+'.olean';p=next((root/rel for root in roots if (root/rel).exists()),None);h=sha(p) if p else None
 checks.append(dict(module=r['module'],selected_path=str(p),expected=r['object_sha256'],actual=h,ok=h==r['object_sha256']))
errors=[r for r in checks if not r['ok']];objects=[]
for r in json.loads((D/'frozen-proof-manifest.json').read_text())['modules']:
 m=r['module'];s=D/'lean-sources'/(m+'.lean');o=D/'lean-objects'/(m+'.olean');assert sha(s)==r['source_sha256'],m
 imports=re.findall(r'^import (\S+)',s.read_text(),re.M);deps=[]
 for imp in imports:
  rel=imp.replace('.','/')+'.olean';p=next((root/rel for root in roots if (root/rel).exists()),None);assert p,imp
  deps.append(dict(module=imp,selected_path=str(p),object_sha256=sha(p)))
 objects.append(dict(**r,object_path=str(o),object_sha256=sha(o),object_bytes=o.stat().st_size,imports=deps))
# Source associations for the exact canonical EJR closure used in InstanceAudit.
ejr=[]
for m,r in json.loads((D/'sampler-cache-pins.json').read_text()).items():
 if r['authority']!='EJR':continue
 rel=m.replace('.','/');s=D/'lean-sources'/(rel+'.lean')
 if not s.exists():s=D.parent/'aspis-joint-20261019/sources'/(rel+'.lean')
 assert sha(s)==r['sha256'],m
 p=next((root/(rel+'.olean') for root in roots if (root/(rel+'.olean')).exists()),None);assert p,m
 ejr.append(dict(module=m,source_path=str(s),source_sha256=sha(s),object_path=str(p),object_sha256=sha(p),authority=r['authority']))
result=dict(external_checks=checks,external_errors=errors,owned_objects=objects,canonical_ejr_objects=ejr,env=env,private_batch2_objects_reused=False)
raw=json.dumps(result,indent=2).encode();(D/'final-dependency-fingerprint.json.xz').write_bytes(lzma.compress(raw,preset=6));(D/'final-dependency-fingerprint.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(external_count=len(checks),external_errors=errors,owned_objects=len(objects),canonical_ejr_objects=len(ejr),private_batch2_objects_reused=False)))
assert not errors
