# Prefix-owned seed: copy retained exports in mandated order, never write predecessors.
import json,hashlib,shutil
from pathlib import Path
records=[]
for m in json.loads((b/'NLH_SEED_INPUTS.json').read_text()):
 origin=Path(m['path']);dest=b/('NLH_'+m['label']+'_seed')
 for e in m['files']:
  src=Path(e['path']);dst=dest/src.relative_to(origin)
  assert hashlib.sha256(src.read_bytes()).hexdigest()==e['sha256'],str(src)
  dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():shutil.copyfile(src,dst)
  assert hashlib.sha256(dst.read_bytes()).hexdigest()==e['sha256'],str(dst)
  records.append(dict(path=str(dst),source=str(src),sha256=e['sha256'],bytes=dst.stat().st_size))
(b/'NLH_SEED.json').write_text(json.dumps(dict(files=records,total_bytes=sum(e['bytes'] for e in records))))
