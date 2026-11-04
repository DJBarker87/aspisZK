"""Delete only owned rebuildable outputs after verifying retained proof exports."""
from pathlib import Path
import json,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-history-persist-20261105')
rows=json.loads((B/'NGR_EXPORT.json').read_text());assert len(rows)==5
for row in rows:
 p=Path(row['path']);assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
removed=[]
for name in ['NGR_objects','NGR_native','NGR_tmp']:
 base=B/name
 for p in sorted(base.rglob('*'),key=lambda p:len(p.parts),reverse=True):
  if p.is_file():
   removed.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()));p.unlink()
  elif p.is_dir():p.rmdir()
 base.rmdir()
result=dict(removed=removed,removed_bytes=sum(r['bytes'] for r in removed),cache_and_exports_retained=True)
(B/'NGR_CLEANUP.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='removed'}))
