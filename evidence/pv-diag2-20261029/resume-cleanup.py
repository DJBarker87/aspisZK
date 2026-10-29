from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029')
assert json.loads((D/'final-cohort-post.json').read_text())['mismatches']==[]
rows=[]
for p in (D/'objects').rglob('*'):
 if p.is_file() and not p.is_symlink(): rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
removed=[]
for name in ['error-exit','retry-control','mapper-control','wire-equality','log-guard']:
 p=D/name
 if p.is_file():
  removed.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size));p.unlink()
shutil.rmtree(D/'objects')
(D/'resume-cleanup.json').write_text(json.dumps(dict(artifact_pins=rows,removed_executables=removed,removed_private_objects=True,other_jobs_modified=False,key_operations=0),indent=2)+'\n')
print('pinned',len(rows),'private object artifacts; removed own compiled scratch and',len(removed),'executables; no key operations')
