from NFB_remote import *
import json
assert not (E/'NFB_ACTIVE.json').exists()
a='NFB_PEER_COHORT_RELOCATE';admit(a)
rows=json.loads((E/'NFB_PEER_COHORT_PINS.json').read_text())
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json
cache=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose5-cache-20261029');root=cache/'NFB_reconcile_objects';out=[]
for item in {rows!r}:
 p=Path(item['destination'])
 if not p.exists():continue # Earlier library relocations are independently pinned.
 assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256']
 q=root/p.relative_to(cache);q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists();p.rename(q)
 out.append(dict(old=str(p),new=str(q),sha256=item['sha256']))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
(E/'NFB_PEER_COHORT_RELOCATIONS.json').write_text(r.stdout)
