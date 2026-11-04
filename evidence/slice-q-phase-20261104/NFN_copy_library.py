from NFN_remote import *
admit('NFN_LIBRARY_COPY')
r=ssh('NFN_LIBRARY_COPY','python3',f'''from pathlib import Path
import os,hashlib,json
src=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose6-cache-20261104/NFG_standard_view');dst=Path({B!r}).parent/'codex-cx-slice-q-phase-cache-20261104'/'NFG_standard_view';rows=[]
for root,dirs,files in os.walk(src,followlinks=True):
 for name in files:
  p=Path(root)/name;q=dst/p.relative_to(src);data=p.read_bytes();q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():q.write_bytes(data)
  assert hashlib.sha256(q.read_bytes()).digest()==hashlib.sha256(data).digest()
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
print(json.dumps(rows))
''');assert r.returncode==0,r.stderr
(E/'NFN_LIBRARY_COPY.json').write_text(r.stdout)
print(len(json.loads(r.stdout)))
