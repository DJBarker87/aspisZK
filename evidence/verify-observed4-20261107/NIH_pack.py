"""Lossless content addressing of this job's repeated source snapshots only."""
from pathlib import Path
import hashlib,json,os
E=Path(__file__).resolve().parent;D=E/'NIH_INPUTS';D.mkdir(exist_ok=True);rows=[]
for folder in sorted(E.glob('NIH_[LKE][0-9][0-9][0-9]')):
 for p in sorted((folder/'sources').rglob('*')):
  if not p.is_file():continue
  data=p.read_bytes();h=hashlib.sha256(data).hexdigest();q=D/(h+'.txt')
  if not q.exists():q.write_bytes(data)
  assert q.read_bytes()==data
  if not p.is_symlink():p.unlink();p.symlink_to(os.path.relpath(q,p.parent))
  rows.append(dict(path=str(p.relative_to(E)),sha256=h,bytes=len(data),stored=str(q.relative_to(E))))
(E/'NIH_SOURCE_STORE.json').write_text(json.dumps(dict(paths=rows),indent=2)+'\n')
