from NFB_remote import *
assert not (E/'NFB_ACTIVE.json').exists()
a='NFB_PEER_LIBRARY_VIEW';admit(a)
r=ssh(a,'python3',f'''from pathlib import Path
import json,hashlib
c=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose5-cache-20261029')
p=c/'Aeneas';q=c/'NFB_retained_peer_Aeneas';pins=[]
if p.exists():
 assert not q.exists()
 for f in p.rglob('*'):
  if f.is_file():pins.append(dict(old=str(f),new=str(q/f.relative_to(p)),sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
 p.rename(q)
print(json.dumps(dict(reason='Reconcile-cache intake accidentally shadowed the pinned SInt2 Aeneas library with incomplete .olean companions. Retain those bytes off the resolved path; original coherent library resolves again. No cache is deleted.',relocations=pins)))
''');assert r.returncode==0,r.stderr
(E/'NFB_PEER_LIBRARY_VIEW.json').write_text(r.stdout)
