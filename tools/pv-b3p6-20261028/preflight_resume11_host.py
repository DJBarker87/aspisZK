"""Read-only external and retained private-object checks before any attempt."""
from pathlib import Path
import json,hashlib,time
from run import H
rows=json.loads((H/'external-object-manifest.json').read_text());bad=[]
for r in rows:
 p=Path(r['path']);h=hashlib.sha256(p.read_bytes()).hexdigest()if p.is_file()else None
 if h!=r['object_sha256']:bad.append(dict(module=r['module'],expected=r['object_sha256'],actual=h))
x=dict(checked_before_any_compile=True,checked_count=len(rows),mismatches=bad,epoch=time.time(),manifest_sha256=hashlib.sha256((H/'external-object-manifest.json').read_bytes()).hexdigest())
(H/'external-verification-resume11.json').write_text(json.dumps(x,indent=2)+'\n');assert not bad,bad
# Validate inherited private cache with the last successful receipt for each module.
latest={}
for p in H.glob('lean-*/receipt/receipt.json'):
 r=json.loads(p.read_text())
 if r.get('exit_status')==0 and 'module'in r:latest[r['module']]=r
bad=[];checked=[]
for m,r in latest.items():
 p=H/'lean-objects'/(m.replace('.','/')+'.olean');s=H/'lean'/(m.replace('.','/')+'.lean')
 if not p.exists():continue
 if not s.exists()or hashlib.sha256(s.read_bytes()).hexdigest()!=r['source_sha256']:
  # Rejected newer drafts are not accepted imports.
  continue
 checked.append(dict(module=m,object_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_sha256=r['source_sha256']))
 for dep,record in r.get('dependency_objects',{}).items():
  q=Path(record['path'])
  if not q.exists()or hashlib.sha256(q.read_bytes()).hexdigest()!=record['sha256']:bad.append(dict(module=m,dependency=dep,path=str(q)))
x=dict(checked_count=len(checked),objects=checked,mismatches=bad,epoch=time.time())
(H/'cache-verification-resume11.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(external=len(rows),private=len(checked),mismatches=bad)));assert not bad,bad
