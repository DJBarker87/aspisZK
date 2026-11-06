from pathlib import Path
import json,shutil
B=Path(__file__).resolve().parent;root=B/'NJR_tmp';rows=[]
for p in root.rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem')):
  rows.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
(B/'NJR_PRUNE.json').write_text(json.dumps(dict(removed=rows,only_own_tmpdir=True,free_bytes=shutil.disk_usage(B).free),indent=2)+'\n')
print(json.dumps(dict(removed=len(rows),bytes=sum(r['bytes'] for r in rows))))
