"""Read-only authority, object, and ID audit. Creates only this job's plan."""
from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2e-20261029')
x=json.loads((D/'inherited-resolution.json').read_text());e=json.loads((D/'env-J.json').read_text());roots=list(map(Path,e['LEAN_PATH'].split(':')))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
for m,r in x['external'].items():
 p=next((d/(m.replace('.','/')+'.olean') for d in roots if(d/(m.replace('.','/')+'.olean')).exists()),None)
 checks.append(dict(module=m,path=str(p),expected=r['object_sha256'],actual=sha(p) if p else None,ok=bool(p) and sha(p)==r['object_sha256']))
old=json.loads((D/'canonical-pins.json').read_text());pins={r['module']:r for r in old};project=[];build=[]
for m in x['order']:
 r=x['modules'][m];rel=m.replace('.','/')
 p=next((d/(rel+'.olean') for d in roots if(d/(rel+'.olean')).exists()),None)
 pin=pins.get(m)
 s=D/'lean-sources'/(rel+'.lean');assert sha(s)==r['sha256'],m
 if pin and p and sha(p)==pin['object_sha256'] and r['sha256']==pin['source_sha256']:
  project.append(dict(module=m,path=str(p),source_sha256=r['sha256'],object_sha256=sha(p),authority=r['authority'],ok=True))
 else:build.append(m)
collisions=[]
for d in D.parent.glob('codex-pv-*'):
 if d==D:continue
 for p in d.glob('lean-622[0-9][0-9]'):collisions.append(str(p))
 for p in d.glob('**/sent.txt'):
  for line in p.read_text(errors='replace').splitlines():
   if re.search(r'\b622\d\d\b',line):collisions.append(dict(path=str(p),line=line))
p=D.parent/'r1-privacy-build-integration-20261019/evidence/sent.txt'
if p.exists():
 for line in p.read_text().splitlines():
  if re.search(r'\b622\d\d\b',line):collisions.append(dict(path=str(p),line=line))
r=dict(external=checks,canonical_reuse=project,private_build_order=build,id_collisions=collisions,toolchain=e,private_cache_reuse=False,reason='RDB2D and RDB2C private objects were removed; canonical objects reused under their EJR/replay authority, not guessed from paths')
(D/'preflight.json').write_text(json.dumps(r,indent=2));print(json.dumps(dict(external=len(checks),external_errors=[c for c in checks if not c['ok']],canonical_reuse=len(project),private_build_order=build,id_collisions=collisions)),flush=True)
assert all(c['ok'] for c in checks) and not collisions
