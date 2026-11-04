from NFB_remote import *
assert not (E/'NFB_ACTIVE.json').exists()
a='NFB_EXTRA_CACHE_INPUT';admit(a)
r=ssh(a,'python3',f'''from pathlib import Path
import json,hashlib
c=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose5-cache-20261029')
p=c/'NDI_objects/NDI_IteratorFrame.olean';q=c/'NDI_IteratorFrame.olean'
data=p.read_bytes()
if q.exists():assert q.read_bytes()==data
else:q.write_bytes(data)
print(json.dumps(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),action='private cache promotion of a copied, pinned, unchanged dependency; predecessor caches untouched')))
''');assert r.returncode==0,r.stderr;(E/'NFB_EXTRA_CACHE.json').write_text(r.stdout)
