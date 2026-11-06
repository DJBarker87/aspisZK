# Private seed copies only; immutable predecessor hash validation on every call.
import json,hashlib,shutil
from pathlib import Path
records=[]
for label in ['NKI','NKN']:
 m=json.loads((b/('NKR_'+label+'_EXPORT.json')).read_text());origin=Path(m['export']);dest=b/('NKR_'+label+'_seed')
 for entry in m['files']:
  src=Path(entry['path']);dst=dest/src.relative_to(origin)
  assert hashlib.sha256(src.read_bytes()).hexdigest()==entry['sha256'],str(src)
  dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():shutil.copyfile(src,dst)
  assert hashlib.sha256(dst.read_bytes()).hexdigest()==entry['sha256'],str(dst)
  records.append(dict(path=str(dst),source=str(src),sha256=entry['sha256'],bytes=dst.stat().st_size))
(b/'NKR_SEED.json').write_text(json.dumps(dict(files=records,total_bytes=sum(r['bytes'] for r in records))))
