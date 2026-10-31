"""Read-only h4 external verification before the first Lean compile."""
from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028/rdcd4-20261029')
e=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'))
roots=[Path(x) for x in e['LEAN_PATH'].split(':')]
manifest=json.load(open(D/'external-object-manifest.json'));out=[];bad=[]
for r in manifest:
 p=Path(r['path'])
 if not p.exists():p=None
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 x=dict(module=r['module'],path=str(p),expected=r['object_sha256'],actual=h)
 out.append(x)
 if h!=r['object_sha256']:bad.append(x)
(D/'preflight-results.json').write_text(json.dumps(dict(checked=out,bad=bad),indent=2)+'\n')
print('External preflight',len(out),'objects;',len(bad),'mismatches')
for x in bad:print(json.dumps(x))
assert not bad,'External authority mismatch: stop affected import steps, never substitute or rebuild'
(D/'lean-objects/R1Z').mkdir(parents=True,exist_ok=True)
# Load the authority's exact objects through an own read-only symlink overlay.
# This is namespace selection, not rebuilding or replacing a library object.
for r in manifest:
 p=Path(r['path']);q=D/'external-objects'/(r['module']+'.olean')
 q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p)
 for suffix in ['.ir','.olean.server','.olean.private']:
  a=p.with_suffix(suffix);b=q.with_suffix(suffix)
  if a.exists() and not b.exists():b.symlink_to(a)
e['LEAN_PATH']=str(D/'lean-objects')+':'+str(D/'external-objects')+':'+e['LEAN_PATH']
roots=[Path(x) for x in e['LEAN_PATH'].split(':')]
for r in manifest:
 p=next(root/(r['module']+'.olean') for root in roots if (root/(r['module']+'.olean')).exists())
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['object_sha256'],r['module']
(D/'env-J.json').write_text(json.dumps(e,indent=2)+'\n')
