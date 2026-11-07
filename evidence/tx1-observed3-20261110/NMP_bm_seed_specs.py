from pathlib import Path
import hashlib,json,shutil
B=Path(__file__).resolve().parent
source=Path('/home/dombarker/project-offloads/codex-cx-tx1-owned-20261111/NMT_objects')
rows=[]
for n in json.loads((B/'NMP_BM_RSL_SOURCE_PINS.json').read_text()):
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=source/(n['module']+suffix)
  if not p.exists():continue
  q=B/'NMP_objects'/p.name
  assert not q.exists(),str(q)
  raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();shutil.copyfile(p,q)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
  rows.append(dict(source=str(p),destination=str(q),sha256=h,bytes=len(raw)))
assert sum(x['source'].endswith('.olean') for x in rows)==5
(B/'NMP_BM_RSL_OBJECT_PINS.json').write_text(json.dumps(rows,indent=1)+'\n')
print('Copied five canonical RSL object closures with source/receipt provenance')
