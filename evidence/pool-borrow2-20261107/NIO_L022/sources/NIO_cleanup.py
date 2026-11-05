"""Remove only rebuildable NIO target scratch after verified cache export."""
from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent
x=json.loads((B/'NIO_EXPORT.json').read_text())
for row in x['exports']:
 p=Path(row['path']);assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
removed=[]
for n in ['NIO_target','NIO_extract_target','NIO_objects','NIO_native','NIO_tmp','NIO_stage/__pycache__']:
 p=B/n
 if p.is_dir():
  assert not p.is_symlink() and p.resolve().is_relative_to(B.resolve())
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
(B/'NIO_CLEANUP.json').write_text(json.dumps(dict(removed=removed,retained_cache=x['cache_retained'],keys_touched=False),indent=1)+'\n')
print('NIO rebuildable target scratch removed; prefix cache retained')
