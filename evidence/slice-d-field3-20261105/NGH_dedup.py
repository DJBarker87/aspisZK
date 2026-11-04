from pathlib import Path
import hashlib,json,os
E=Path(__file__).resolve().parent;B=E/'NGH_inputs';B.mkdir(exist_ok=True);rows=[]
for directory in E.glob('NGH_[KLE]???/sources'):
 for p in directory.rglob('*'):
  if not p.is_file():continue
  data=p.read_bytes();sha=hashlib.sha256(data).hexdigest();dst=B/(sha+'.txt')
  if not dst.exists():dst.write_bytes(data)
  assert dst.read_bytes()==data
  if not p.is_symlink():p.unlink();p.symlink_to(os.path.relpath(dst,p.parent))
  rows.append(dict(path=str(p.relative_to(E)),sha256=sha,blob=str(dst.relative_to(E))))
(E/'NGH_SNAPSHOT_DEDUP.json').write_text(json.dumps(rows,indent=1)+'\n')
print(json.dumps(dict(snapshot_files=len(rows),unique_inputs=len(list(B.iterdir())))))
