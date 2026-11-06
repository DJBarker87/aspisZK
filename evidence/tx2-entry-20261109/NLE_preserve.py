from NLE_transport import *
import json
admission('NLE_S005')
r=ssh('python3',f'''from pathlib import Path
import shutil,hashlib,json
b=Path({B!r});dst=b/'NLE_stage2_objects';dst.mkdir(exist_ok=True);rows=[]
for p in sorted((b/'NLE_objects').rglob('*')):
 if p.is_file():
  q=dst/p.relative_to(b/'NLE_objects');q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():shutil.copy2(p,q)
  rows.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
print(json.dumps(dict(files=rows,bytes=sum(r['bytes'] for r in rows))))
''');assert r.returncode==0,r.stderr
(E/'NLE_STAGE2_OBJECTS.json').write_text(r.stdout);print('NLE stage2 objects retained')
