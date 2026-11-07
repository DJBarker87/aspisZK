from pathlib import Path
import hashlib,json,shutil
B=Path(__file__).resolve().parent
source=Path('/home/dombarker/project-offloads/codex-cx-tx1-owned-20261111/NMT_objects')
rows=[]
for name in ['NMT_tx1/Types','NMT_TransportBase']:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=source/(name+suffix)
  if not p.exists():continue
  q=B/'NMP_objects'/(name+suffix);q.parent.mkdir(parents=True,exist_ok=True)
  assert not q.exists(),str(q)
  raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();shutil.copyfile(p,q)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
  rows.append(dict(source=str(p),destination=str(q),sha256=h,bytes=len(raw)))
assert sum(x['source'].endswith('.olean') for x in rows)==2
(B/'NMP_BM_TRANSPORT_OBJECT_PINS.json').write_text(json.dumps(rows,indent=1)+'\n')
print('Copied existing generic NMT transport helper and its fresh-types dependency')
