"""Remove only this job's completed rebuildable caches, retaining sources/receipts."""
from pathlib import Path
import hashlib,json,subprocess,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-extraction-assoc3-20261027')
commands=subprocess.check_output(['ps','-eo','args='],text=True).splitlines()
active=[s for s in commands if str(B) in s and any(t in s for t in ['lean -j1','cargo-kani kani','cbmc --','S2W_lean_host.py XRk','S2W_run_host.py XRk'])]
assert not active,active
objects=[]
for p in sorted((B/'XRk_objects').rglob('*')):
 if not p.is_file():continue
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 objects.append({'path':str(p.relative_to(B)),'bytes':p.stat().st_size,'sha256':h.hexdigest()})
removed=[]
for name in ['XRk_target','XRk_objects','XRk_crate','.lake']:
 p=B/name
 if not p.exists():continue
 size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file() and not q.is_symlink())
 shutil.rmtree(p);removed.append({'path':str(p),'bytes':size})
receipt={'active_own_build_processes':active,'removed':removed,'object_manifest':objects,'solver_temps':'No /tmp solver filename with attributable ownership was emitted by these Kani runs; unrelated temporary files were not deleted.','retained':'All sources, source snapshots, receipts, coherent shared caches, keys, and other jobs remain untouched. No wallet/account key was created or cleaned up.'}
(B/'XRk_cleanup.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'removed_bytes':sum(r['bytes'] for r in removed),'objects_hashed':len(objects),'active':active}))
