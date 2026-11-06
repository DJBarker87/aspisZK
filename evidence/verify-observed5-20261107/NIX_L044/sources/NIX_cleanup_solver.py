from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent;items=[]
# Only this job's TMPDIR, after all previous clients have drained. No shared /tmp deletion.
for p in sorted((B/'NIX_tmp').rglob('*')):
 if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem') or p.suffix in ['.cnf','.smt2']):
  items.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()));p.unlink()
(B/'NIX_SOLVER_CLEANUP.json').write_text(json.dumps(dict(removed=items,private_tmp=str(B/'NIX_tmp'),shared_tmp='not deleted: no attributable path retained for K017'),indent=2));print('NIX own solver temporary files removed',len(items))
