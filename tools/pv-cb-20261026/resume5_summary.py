"""Check charged budgets and produce a truthful live native table from receipts."""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026'
t=json.loads((ev/'RESUME5-TALLY.json').read_text())
lean=[]
for p in ev.glob('*.json'):
 if p.stem.isdigit() and 41200<=int(p.stem)<=41499:
  r=json.loads(p.read_text())
  if 'module' in r and 'exit' in r:lean.append(r)
assert len(lean)==t['lean_charged'],(len(lean),t['lean_charged'])
assert len({a['id'] for a in t['attempts']})==len(t['attempts'])
assert t['lean_charged']<=100 and t['kani_charged']<=12
rows=[]
for run in t.get('kani_runs',[]):
 p=ev/run['name']/'collected-receipt.json'
 if not p.exists():rows.append((run['harness'],'pending',str(run['timeout_seconds']),'running','pending'));continue
 r=json.loads(p.read_text());assert r['attempt_charged']
 h=r.get('harness',run['harness']);bound=r.get('unwind_bound')
 if bound is None:bound=18 if h.startswith('compress') else 30 if h.startswith('horner_index') else 40 if h=='circle_sample_reference' else 1026 if h=='pole1024_reference' else 'see target'
 log=(p.parent/'output.log').read_text();code=int(r['exit'])
 verdict='timeout; no verdict' if code==124 else 'VERIFIED' if code==0 and 'VERIFICATION:- SUCCESSFUL' in log and 'successfully verified harnesses' in log else 'inspect failure; no row credit'
 rows.append((h,str(bound),str(r.get('timeout_seconds',run.get('timeout_seconds',900))),r['wall'],verdict))
s=('# Resume5 native gates (final)' if t['kani_charged']==12 and all(x.get('state')=='complete' for x in t.get('kani_runs',[])) else '# Resume5 native gates (live)')+'\n\n'
s+='|harness|unwind|timeout s|wall|verdict|\n|---|---:|---:|---|---|\n'
for row in rows:s+='|'+'|'.join(row)+'|\n'
s+='\nA timeout is neither a proof nor a counterexample. Each named directory retains target argv, source/input hashes, caps, exit, GNU time metrics and separate sampled cgroup observations when available. Timeout GNU RSS is wrapper rusage, not an invented final aggregate peak. Source/Lean axioms receipts are separate.\n'
(ev/'RESUME5-KANI-TABLE.md').write_text(s)
summary=dict(lean_charged=len(lean),lean_passed=sum(r['exit']==0 for r in lean),lean_failed=sum(r['exit']!=0 for r in lean),kani_charged=t['kani_charged'],kani_recorded=len(rows),next_unused_env_j_id=t['next_env_j_id'],final_lean_attempts_reserved=3,rows_removed=0,endpoint_premises_removed=0,stable_op223_source_present=(root/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB_Op223Source.lean').exists(),target='not yet established')
(ev/'RESUME5-COUNTS.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
