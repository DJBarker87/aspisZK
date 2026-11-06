from pathlib import Path
import json,shutil
B=Path(__file__).resolve().parent;removed=[]
for name in ['NJR_target','NJR_tmp']:
 p=B/name
 if p.is_dir():
  size=sum(f.stat().st_size for f in p.rglob('*') if f.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
result=dict(removed=removed,retained_cache='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJR_exports_20261108',cache_deleted=False,free_bytes=shutil.disk_usage(B).free)
(B/'NJR_CLEANUP.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
