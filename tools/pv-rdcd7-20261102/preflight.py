"""Verify every external object in situ; do not copy or rebuild libraries."""
from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd7-20261102')
e=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'))
roots=[Path(x) for x in e['LEAN_PATH'].split(':')]
def obj(m):
 r=next((r for r in roots if (r/m.split('/')[0]).is_dir()),None)
 return r/(m+'.olean') if r else None
rows=[]
for pin in json.load(open(D/'external-object-manifest.json')):
 p=obj(pin['module']);assert p and p.exists(),pin['module']
 h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==pin['object_sha256'],(pin['module'],str(p),h,pin['object_sha256'])
 rows.append(dict(module=pin['module'],path=str(p),sha256=h))
e['LEAN_PATH']=str(D/'lean-objects')+':'+e['LEAN_PATH']
(D/'env-J.json').write_text(json.dumps(e,indent=2)+'\n')
(D/'preflight-result.json').write_text(json.dumps(dict(environment=e,external=rows,external_count=len(rows),reused={},status='verified effective first-root external resolution in situ; private R1Z namespace to be built in dependency order'),indent=2)+'\n')
print('Verified',len(rows),'external objects; no cached project objects accepted')
