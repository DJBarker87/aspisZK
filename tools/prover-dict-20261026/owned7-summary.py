"""Read-only indexing of owned-reference native evidence, including failures."""
from pathlib import Path
import json,hashlib,subprocess
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/owned7'
rows=[]
for p in sorted(e.glob('pdict-*')):
 if not p.is_dir():continue
 q=p/'receipt.json'
 if q.exists():
  x=json.loads(q.read_text());rows.append({k:x.get(k) for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','cgroup_swap_peak_bytes','target','limits','print_axioms','expected_work']})
 elif (p/'manual-stop.json').exists():
  rows.append(dict(attempt=p.name,exit_status='scope stopped explicitly',wall_seconds=None,peak_rss_kib=None,swaps=None,qualification='Constant-EINTR retry path isolated and stopped; stopping the entire scope also killed the receipt writer. Final resource counters unavailable. Rejected, no validation claim. See preflight/time/stdout and manual-stop.'))
rows.sort(key=lambda x:int(x['attempt'].split('-')[-1]));assert len({x['attempt'] for x in rows})==len(rows)
(e/'native-summary.json').write_text(json.dumps(dict(runs=rows,kani_runs=len(rows),remaining=15-len(rows),passed=sum(x['exit_status']==0 for x in rows),root_premises_removed=0,qualification='Native observations only, with explicit schedule restrictions. Standard C ABI symbols are rooted and traced, not Kani stubs. Actual OS ownership/world adequacy and whole caller composition remain open.'),indent=2)+'\n')
print(len(rows),'Kani runs;',15-len(rows),'remain')
