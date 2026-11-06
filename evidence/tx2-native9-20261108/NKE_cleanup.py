"""Remove ONLY this job's abandoned solver temporaries; retain all caches."""
from pathlib import Path
import json,shutil
B=Path(__file__).resolve().parent;tmp=B/'NKE_tmp';removed=[]
for p in sorted(tmp.rglob('*')):
 if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem')):
  removed.append({'path':str(p),'bytes':p.stat().st_size});p.unlink()
(B/'NKE_CLEANUP.json').write_text(json.dumps({'removed_solver_files':removed,'bytes':sum(r['bytes'] for r in removed),'free_bytes':shutil.disk_usage(B).free,'retained_cache':True,'CARGO_TARGET_DIR':str(B/'NKE_target')},indent=2)+'\n')
print(json.dumps({'removed_solver_files':len(removed),'bytes':sum(r['bytes'] for r in removed),'free_bytes':shutil.disk_usage(B).free}))
