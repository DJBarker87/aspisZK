# Executed by the NKI input client before launch, only private copies are written.
import json,hashlib,shutil
from pathlib import Path
records=[]
for manifest_name,own,field in [('NKI_PREDECESSOR_EXPORT.json','NKI_seed','export_dir'),('NKI_NKC_EXPORT.json','NKI_NKC_seed','export')]:
 m=json.loads((b/manifest_name).read_text()); origin=Path(m[field]); dest=b/own
 for entry in m['files']:
  src=Path(entry['path']); relative=src.relative_to(origin); dst=dest/relative
  assert hashlib.sha256(src.read_bytes()).hexdigest()==entry['sha256'],str(src)
  dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():shutil.copyfile(src,dst)
  assert hashlib.sha256(dst.read_bytes()).hexdigest()==entry['sha256'],str(dst)
  records.append(dict(path=str(dst),source=str(src),sha256=entry['sha256'],bytes=dst.stat().st_size))
(b/'NKI_SEED.json').write_text(json.dumps(dict(files=records,total_bytes=sum(r['bytes'] for r in records))))
