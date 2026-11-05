"""Lossless content-addressed storage of repeated committed source snapshots."""
from pathlib import Path
import hashlib,json,os
E=Path(__file__).resolve().parent;D=E/'NID_inputs';D.mkdir(exist_ok=True);records=[]
for attempt in sorted(E.glob('NID_[KLE][0-9][0-9][0-9]')):
 if not (attempt/'receipt.json').exists():continue
 receipt=json.loads((attempt/'receipt.json').read_text())
 if receipt['kind']=='kani' and not (E/(attempt.name+'-lock-check.json')).exists():continue
 for p in sorted((attempt/'sources').rglob('*')):
  if not p.is_file() or p.is_symlink():continue
  raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();q=D/h
  if q.exists():assert q.read_bytes()==raw
  else:q.write_bytes(raw)
  rel=os.path.relpath(q,p.parent);p.unlink();p.symlink_to(rel)
  records.append(dict(path=str(p.relative_to(E)),sha256=h,bytes=len(raw),target=str(q.relative_to(E))))
old=json.loads((E/'NID_SOURCE_ARCHIVE.json').read_text()) if (E/'NID_SOURCE_ARCHIVE.json').exists() else []
old={r['path']:r for r in old}
for r in records:old[r['path']]=r
(E/'NID_SOURCE_ARCHIVE.json').write_text(json.dumps(list(old.values()),indent=2)+'\n')
print(json.dumps(dict(new_references=len(records),unique=len(list(D.iterdir())))))
