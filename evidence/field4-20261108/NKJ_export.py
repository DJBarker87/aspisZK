from pathlib import Path
import json,shutil,hashlib
B=Path(__file__).resolve().parent
assert B==Path('/home/dombarker/project-offloads/codex-cx-field4-20261108')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
D=B/'NKJ_exports_20261108';D.mkdir(exist_ok=False);pins=[]
for p in sorted((B/'NKJ_objects').rglob('*')):
 if p.is_file():
  q=D/p.relative_to(B/'NKJ_objects');q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  assert sha(p)==sha(q);pins.append(dict(origin=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
# Keep all seed and compiled object caches. Only private rebuildable Cargo target
# and this job's own solver temporary files are removed, after hash inventory.
cleanup=[]
for root in [B/'NKJ_target',B/'NKJ_tmp']:
 if root.exists():
  for p in root.rglob('*'):
   if p.is_file():cleanup.append(dict(path=str(p),bytes=p.stat().st_size))
  if root.name=='NKJ_target':shutil.rmtree(root)
  else:
   for p in root.rglob('*'):
    if p.is_file() and (p.name.startswith(('external-sat','smt2_dec_problem','smt_dec_problem')) or p.suffix in ['.cnf','.smt2']):p.unlink()
retained=sum(p.stat().st_size for p in B.rglob('*') if p.is_file())
assert retained<30000000000
out=dict(export_root=str(D),files=pins,total_export_bytes=sum(p['bytes'] for p in pins),retained_workspace_bytes=retained,free_bytes=shutil.disk_usage(B).free,CARGO_TARGET_DIR=str(B/'NKJ_target'),cargo_target_removed=True,cache_roots_retained=[str(B/'NKJ_seed'),str(B/'NKJ_objects'),str(D)],cleanup=cleanup,lock_sha256=sha(B/'NKJ_src/Cargo.lock'))
(B/'NKJ_EXPORT.json').write_text(json.dumps(out,indent=2));print('NKJ exports retained; owned build target removed; workspace below30GB')
