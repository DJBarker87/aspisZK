from NFB_remote import *
assert not (E/'NFB_ACTIVE.json').exists()
a='NFB_PEER_ROOT_LIBRARY_VIEW';admit(a)
r=ssh(a,'python3',f'''from pathlib import Path
import json,hashlib
c=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose5-cache-20261029');q=c/'NFB_retained_peer_Aeneas_root';q.mkdir(exist_ok=True);pins=[]
for p in c.glob('Aeneas.*'):
 if not p.is_file():continue
 f=q/p.name;assert not f.exists();pins.append(dict(old=str(p),new=str(f),sha256=hashlib.sha256(p.read_bytes()).hexdigest()));p.rename(f)
print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NFB_PEER_ROOT_LIBRARY_VIEW.json').write_text(r.stdout)
