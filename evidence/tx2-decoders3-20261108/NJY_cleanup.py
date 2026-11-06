from NJY_transport import *
r=ssh('python3',f'''from pathlib import Path
import json,shutil,time
b=Path({B!r});target=b/'NJY_target';assert target.parent==b and not target.is_symlink()
before=shutil.disk_usage(b);size=sum(p.stat().st_size for p in target.rglob('*')if p.is_file())if target.exists()else 0
if target.exists():shutil.rmtree(target)
removed=[]
for p in (b/'NJY_tmp').rglob('*'):
 if p.is_file() and (p.name.startswith(('external-sat','smt2_dec_problem'))or p.suffix in ['.cnf','.smt2']):
  removed.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
retained=[b/'NJY_objects',b/'NJY_NJQ_seed',b/'NJY_NJW_seed',b/'NJY_exports_20261108',b/'NJY_exports_final_20261108',b/'NIJ_src']
assert all(p.is_dir()for p in retained)
print(json.dumps(dict(removed_rebuildable_rust_target=str(target),removed_bytes=size,removed_solver_files=removed,retained=[str(p)for p in retained],before=before._asdict(),after=shutil.disk_usage(b)._asdict(),policy='local-lean9: own compilation target/failed solver scratch only; retained Lean caches and exports untouched')))
''');assert r.returncode==0,r.stderr
(E/'NJY_CLEANUP.json').write_text(r.stdout);x=json.loads(r.stdout);print(json.dumps(dict(cleanup='own rebuildable Rust target only; Lean caches retained',removed_bytes=x['removed_bytes'],free_bytes=x['after']['free'])))
