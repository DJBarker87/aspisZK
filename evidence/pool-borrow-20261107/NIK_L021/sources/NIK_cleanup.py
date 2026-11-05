"""Remove only rebuildable NIK target scratch after verified cache export."""
from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent
x=json.loads((B/'NIK_EXPORT.json').read_text())
for row in x['exports']:
 p=Path(row['path']);assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
removed=[]
for n in ['NIK_mir_target','NIK_extract_target']:
 p=B/n
 if p.is_dir():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
(B/'NIK_CLEANUP.json').write_text(json.dumps(dict(removed=removed,retained_cache=x['cache_retained'],keys_touched=False),indent=1)+'\n')
print('NIK rebuildable target scratch removed; prefix cache retained')
