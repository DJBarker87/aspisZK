"""Read-only cache/source/environment inventory for the exact-environment replay."""
from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2g-20261029');p=json.loads((D/'plan.json').read_text());env=p['environment'];old=D.with_name('codex-pv-rdb2e-20261029');prior=json.loads((old/'env-J.json').read_text());assert env==prior
roots=list(map(Path,env['LEAN_PATH'].split(':')));F=D.with_name('codex-pv-rdb2f-20261029');rows=[]
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
# Inventory only; no missing or mismatched object is staged here.
for r in p['objects']:
 m=r['module'];rel=m.replace('.','/');s=F/'lean-sources'/(rel+'.lean');assert sha(s)==r['source']['sha256'],m
 candidates=[root/(rel+'.olean') for root in roots]
 candidates += list(D.parent.glob('codex-pv-*/lean-objects/'+rel+'.olean'))
 matches=[dict(path=str(q),sha256=sha(q)) for q in dict.fromkeys(candidates) if q.exists() and sha(q)==r['object_sha256']]
 rows.append(dict(module=m,source=r['source'],expected_object_sha256=r['object_sha256'],matches=matches,required=m in p['required_order']))
ext=[]
for r in p['external']:
 q=next(root/(r['module'].replace('.','/')+'.olean') for root in roots if (root/(r['module'].replace('.','/')+'.olean')).exists());assert sha(q)==r['actual'],r['module'];ext.append(dict(module=r['module'],path=str(q),sha256=sha(q)))
coll=[]
for d in D.parent.glob('codex-pv-*'):
 if d==D:continue
 coll.extend(str(q) for q in d.glob('lean-639[0-9][0-9]'))
sent=D.parent/'r1-privacy-build-integration-20261019/evidence/sent.txt'
if sent.exists():coll.extend(l for l in sent.read_text().splitlines() if re.search(r'\b639\d\d\b',l))
assert not coll,coll
j=dict(environment=env,exact_original_environment=True,actual_run2_LEAN_PATH=str(roots[0])+':'+env['LEAN_PATH'],run2_sha256=sha(D.parent/'aspis-fs-generic-20261006/evidence/run2.py'),lean_sha256=sha(Path(env['LEAN'])),source_root=str(F/'lean-sources'),objects=rows,external=ext,collisions=coll,required_targets=len(p['required_order']),missing=[r['module'] for r in rows if not r['matches']])
(D/'preflight.json').write_text(json.dumps(j,indent=2));print(json.dumps(dict(required=len(p['required_order']),missing=len(j['missing']),missing_modules=j['missing'],collisions=coll)))
