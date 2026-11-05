"""Remove only rebuildable NIZ target scratch after verified cache export."""
from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent
x=json.loads((B/'NIZ_EXPORT.json').read_text())
for row in x['exports']:
 p=Path(row['path']);assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
removed=[]
for n in ['NIZ_target','NIZ_extract_target','NIZ_objects','NIZ_native','NIZ_tmp','NIZ_stage/__pycache__']:
 p=B/n
 if p.is_dir():
  assert not p.is_symlink() and p.resolve().is_relative_to(B.resolve())
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
(B/'NIZ_CLEANUP.json').write_text(json.dumps(dict(removed=removed,retained_cache=x['cache_retained'],keys_touched=False),indent=1)+'\n')
print('NIZ rebuildable target scratch removed; prefix cache retained')
