"""Final retention check; remove only own solver temporary files after all scopes."""
from pathlib import Path
import json,shutil
B=Path(__file__).resolve().parent
deleted=[]
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in (B/'NLE_tmp').rglob(pattern):
  if p.is_file() and not p.is_symlink():
   deleted.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
size=sum(p.stat().st_size for p in B.rglob('*') if p.is_file())
assert size<30_000_000_000,size
assert shutil.disk_usage(B).free>=40_000_000_000
assert (B/'NLE_exports_final_20261109').is_dir()
report=dict(workspace=str(B),own_bytes=size,free_bytes=shutil.disk_usage(B).free,cargo_target=str(B/'NLE_target'),cache_retained=True,cache_deleted=False,keys_touched=False,deleted_paths=deleted,cleanup_scope="only own NLE_tmp solver files; all scopes finished; no target/cache/export removal")
for n in ['NLE_RETENTION.json','NLE_CLEANUP.json']:(B/n).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
