from NFB_remote import *
import json
assert not (E/'NFB_ACTIVE.json').exists()
a='NFB_PEER_COHORT_CACHE';admit(a)
r=ssh(a,'python3',f'''from pathlib import Path
import shutil,hashlib,json
src=Path('/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/objects')
dst=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose5-cache-20261029')
pins=[]
for p in src.rglob('*.olean'):
 q=dst/p.relative_to(src)
 if q.exists():continue
 q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 pins.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NFB_PEER_COHORT_PINS.json').write_text(r.stdout)
