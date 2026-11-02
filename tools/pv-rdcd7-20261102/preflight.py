"""Verify every external object in a namespace-complete plain-copy overlay; do not copy or rebuild libraries."""
from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd7-20261102')
e=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'))
roots=[D/'external-objects']+[Path(x) for x in e['LEAN_PATH'].split(':')]
def obj(m):
 r=next((r for r in roots if (r/m.split('/')[0]).is_dir()),None)
 return r/(m+'.olean') if r else None
rows=[]
for pin in json.load(open(D/'external-object-manifest.json')):
 original=Path(pin['path']);assert original.exists(),str(original)
 assert hashlib.sha256(original.read_bytes()).hexdigest()==pin['object_sha256'],pin['module']
 p=D/'external-objects'/(pin['module']+'.olean');p.parent.mkdir(parents=True,exist_ok=True)
 for a in [original,*[original.with_suffix(x) for x in ['.ir','.olean.server','.olean.private']]]:
  if a.exists():
   target=p.parent/(p.stem+a.name[len(original.stem):]);shutil.copy2(a,target)
   assert hashlib.sha256(target.read_bytes()).hexdigest()==hashlib.sha256(a.read_bytes()).hexdigest()
 assert obj(pin['module'])==p,pin['module']
 h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==pin['object_sha256'],(pin['module'],str(p),h,pin['object_sha256'])
 rows.append(dict(module=pin['module'],path=str(p),sha256=h))
e['LEAN_PATH']=str(D/'lean-objects')+':'+str(D/'external-objects')+':'+e['LEAN_PATH']
(D/'env-J.json').write_text(json.dumps(e,indent=2)+'\n')
(D/'preflight-result.json').write_text(json.dumps(dict(environment=e,external=rows,external_count=len(rows),reused={},status='verified effective first-root external resolution in a namespace-complete plain-copy overlay; private R1Z namespace to be built in dependency order'),indent=2)+'\n')
print('Verified',len(rows),'external objects; no cached project objects accepted')
