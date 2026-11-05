"""Verify retained own exports before removing only own rebuildable outputs."""
from pathlib import Path
import json,hashlib,shutil
B=Path.cwd();assert B==Path('/home/dombarker/project-offloads/codex-cx-experiment-law-20261106')
x=json.loads((B/'NHZ_EXPORT.json').read_text())
for r in x['exports']:
 p=Path(r['path']);assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
removed=[];total=0
for name in ['NHZ_native','NHZ_objects','NHZ_tmp']:
 p=B/name
 if p.exists():
  size=sum(z.stat().st_size for z in p.rglob('*') if z.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size));total+=size
report=dict(removed=removed,removed_bytes=total,exports_verified=len(x['exports']),cache_retained=x['cache_retained'],disk=shutil.disk_usage(B)._asdict())
(B/'NHZ_CLEANUP.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps(report))
