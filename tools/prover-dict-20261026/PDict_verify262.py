"""Validate retained receipts and final proof sources without compiling."""
from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parents[2]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/formatter262'
allowed={'propext','Classical.choice','Quot.sound'}
latest={};local=[]
for p in sorted((e/'local').glob('*-receipt.json')):
 x=json.loads(p.read_text());local.append(x)
 snapshot=e/'local'/f"{x['attempt']}.lean.txt"
 assert hashlib.sha256(snapshot.read_bytes()).hexdigest()==x['source_sha256']
 if x['exit_status']==0:
  assert 'sorryAx' not in x['print_axioms'] and not re.search(r'error[:(]',x['print_axioms'])
  for report in re.findall(r'depends on axioms: \[([^]]*)\]',x['print_axioms']):
   assert set(z.strip() for z in report.replace('\n','').split(','))<=allowed
  latest[x['module']]=x
for module,x in latest.items():
 p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(module+'.lean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==x['source_sha256'],module
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|^\s*axiom\b',p.read_text(),re.M)
rows=[]
for a in [26200,26201,26202,26203]:
 x=json.loads((e/str(a)/'receipt.json').read_text())
 rows.append({k:x[k] for k in ['attempt','module','source_revision','source_sha256','exit_status','wall','peak_rss_kib','swaps']})
for x in local:
 rows.append({k:x[k] for k in ['attempt','module','source_revision','source_sha256','exit_status','wall_seconds','peak_rss_bytes','swaps']})
assert len(rows)==len(set(x['attempt'] for x in rows))
native=json.loads((e/'native-summary.json').read_text())
summary=dict(lean_budget=100,lean_attempts=len(rows),lean_accepted=sum(x['exit_status']==0 for x in rows),lean_rejected=sum(x['exit_status']!=0 for x in rows),kani_budget=10,kani_runs=native['kani_runs'],next_unused_env_j=max(x['attempt'] for x in rows)+1,latest_accepted_modules={m:x['attempt'] for m,x in latest.items()},attempts=rows,qualification='No failed declaration/sorryAx is accepted. Audit uses cached dependencies; not a release manifest replay. Remaining allocation is unspent, not exhausted; host launch stop is the full filesystem/infrastructure failure.')
(e/'budget.json').write_text(json.dumps(summary,indent=2)+'\n')
(e/'local-summary.json').write_text(json.dumps(dict(latest=[{k:x[k] for k in ['attempt','module','source_revision','source_sha256','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']} for x in latest.values()],source_binding='Every final source byte hash matches its latest accepted snapshot.'),indent=2)+'\n')
print('Lean',len(rows),'accepted',summary['lean_accepted'],'latest modules',len(latest),'Kani',native['kani_runs'])
