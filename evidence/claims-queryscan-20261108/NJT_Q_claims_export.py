from pathlib import Path
import hashlib,json,shutil
B=Path(__file__).resolve().parent;D=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJT_QClaims_exports_20261108');D.mkdir(exist_ok=True);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();pins=[]
for p in sorted((B/'NJT_Q_objects').glob('NJT_QClaims*')):
 if p.is_file():
  q=D/p.name
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copyfile(p,q)
  pins.append(dict(path=str(q),source=str(p),sha256=sha(q),bytes=q.stat().st_size))
(B/'NJT_QCLAIMS_EXPORT.json').write_text(json.dumps(dict(export=str(D),files=pins,total_bytes=sum(p['bytes'] for p in pins),cargo_target_dir=str(B/'NJT_Q_target')),indent=2));print('canonical claims support exported separately; B retained export untouched')
