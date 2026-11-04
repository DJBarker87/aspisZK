"""Remove only this job's rebuildable host scratch after verified export."""
from pathlib import Path
import json,hashlib,shutil,subprocess
b=Path('/home/dombarker/project-offloads/codex-cx-slice-d-checkpoint-20261104');x=json.loads((b/'NGC_EXPORT.json').read_text())
for r in x['objects']:assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['sha256']
# All named directories were created exclusively by this proof job; no wallet,
# account key or deployment action occurred. Retained cache is never a target.
rows=[]
for name in ['NGC_target','NGC_ref_target','NGC_tmp','NGC_objects','NGC_native']:
 p=b/name;assert p.parent==b and name.startswith('NGC_')
 if p.exists():
  size=int(subprocess.check_output(['du','-sb',str(p)],text=True).split()[0]);shutil.rmtree(p);rows.append(dict(path=str(p),bytes=size))
r=dict(status='PASS',removed_rebuildable_scratch=rows,retained_export=x['destination'],retained_cache='/home/dombarker/project-offloads/codex-cx-slice-d-checkpoint-cache-20261104',export_hashes_verified=True,live_jobs_affected=False,disk_after=subprocess.check_output(['df','-B1',str(b)],text=True))
(b/'NGC_CLEANUP.json').write_text(json.dumps(r,indent=1)+'\n');print(json.dumps(r))
