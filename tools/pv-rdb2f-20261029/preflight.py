"""Validate the inherited sources and complete immutable object cohort; mask affected caches."""
from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2f-20261029');old=D.with_name('codex-pv-rdb2e-20261029')
x=json.loads((D/'inherited-resolution.json').read_text());env=json.loads((D/'env-J.json').read_text());prior=json.loads((old/'env-J.json').read_text());assert env['LEAN_PATH'].replace(str(D),str(old))==prior['LEAN_PATH'];assert {k:v for k,v in env.items()if k!='LEAN_PATH'}=={k:v for k,v in prior.items()if k!='LEAN_PATH'}
roots=list(map(Path,env['LEAN_PATH'].split(':')))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def find(m):return next((p/(m.replace('.','/')+'.olean') for p in roots if(p/(m.replace('.','/')+'.olean')).exists()),None)
ext=[]
for m,r in x['external'].items():
 p=find(m);h=sha(p)if p else None;ext.append(dict(module=m,path=str(p),expected=r['object_sha256'],actual=h));assert h==r['object_sha256'],m
pins={r['module']:r for r in json.loads((D/'canonical-pins.json').read_text())};fresh=set(json.loads((D/'fresh-order.json').read_text()));reuse=[];build=[]
for m in x['order']:
 r=x['modules'][m];s=D/'lean-sources'/(m.replace('.','/')+'.lean');assert sha(s)==r['sha256'],m
 if m in fresh:build.append(m);continue
 p=find(m);pin=pins.get(m)
 if p and pin and sha(p)==pin['object_sha256'] and r['sha256']==pin['source_sha256']:
  assert not any(i in fresh for i in r['imports']),m
  reuse.append(dict(module=m,path=str(p),source_sha256=r['sha256'],object_sha256=sha(p),imports=[dict(module=i,path=str(find(i)),object_sha256=sha(find(i))) for i in r['imports']]))
 else:build.append(m)
collisions=[]
for d in D.parent.glob('codex-pv-*'):
 if d==D:continue
 for p in d.glob('lean-633[0-9][0-9]'):collisions.append(str(p))
 for p in d.glob('**/sent.txt'):
  for line in p.read_text(errors='replace').splitlines():
   if re.search(r'\b633\d\d\b',line):collisions.append(dict(path=str(p),line=line))
p=D.parent/'r1-privacy-build-integration-20261019/evidence/sent.txt'
if p.exists():
 for line in p.read_text().splitlines():
  if re.search(r'\b633\d\d\b',line):collisions.append(dict(path=str(p),line=line))
assert not collisions,collisions
j=dict(external=ext,reuse=reuse,build_order=build,fresh_required=sorted(fresh),environment=env,prior_environment=prior,LEAN_PATH_change='private leading directory renamed only; identical toolchain and complete external prefix',id_collisions=collisions)
(D/'preflight.json').write_text(json.dumps(j,indent=2));print(json.dumps(dict(external=len(ext),reuse=len(reuse),build_order=build,id_collisions=collisions)))
