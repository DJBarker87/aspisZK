from pathlib import Path
import json,re
B=Path(__file__).resolve().parent;records=[]
paths=set()
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 paths.update((B/'NIY_tmp').rglob(pattern))
logs=[B/a/'stdout.log' for a in ['NIY_K035','NIY_K051']]
for log in logs:
 if not log.exists():continue
 for n in re.findall(r'/tmp/(?:external-sat[^\s\"\']*\.cnf|smt2_dec_problem[^\s\"\']*)',log.read_text()):paths.add(Path(n))
for p in sorted(paths):
 if p.is_file():
  records.append(dict(path=str(p),bytes=p.stat().st_size,ownership='own TMPDIR or exact K035 log path'));p.unlink()
(B/'NIY_CLEANUP.json').write_text(json.dumps(dict(after='NIY_K035/K051 excluded timeouts',removed=records,bytes=sum(r['bytes'] for r in records),shared_paths_scanned=False,cache_deleted=False),indent=2)+'\n')
print(json.dumps(dict(removed=len(records),bytes=sum(r['bytes'] for r in records))))
