"""Collect focused receipts from retained raw inputs and logs; no launches."""
from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/resumed144';rows=[]
for p in sorted(e.glob('144*-input.json')):
 x=json.loads(p.read_text());a=x['attempt']
 if a==14400:continue
 assert hashlib.sha256((e/f'{a}.lean.txt').read_bytes()).hexdigest()==x['source_sha256']
 log=(e/f'out-{a}.log').read_text() if (e/f'out-{a}.log').exists() else '';t=(e/f'time-{a}.log').read_text() if (e/f'time-{a}.log').exists() else '';m=re.search(r'^exit=(\d+)',log,re.M);status=int(m[1]) if m else None
 reports=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)
 if status==0:
  assert 'sorryAx' not in log and 'error:' not in log
  for z in reports:
   if 'depends on axioms: [' in z:assert set(v.strip() for v in z.split('depends on axioms: [')[1][:-1].replace('\n','').split(','))<={'propext','Classical.choice','Quot.sound'}
 x.update(exit_status=status,command=f"sh {x['launcher']} {a} {x['module']} J 7000 8 {x['deps_fingerprint']}",time_log=t,print_axioms=reports,errors=[z for z in log.splitlines() if 'error:' in z],disposition='Accepted focused proof; no release claim' if status==0 else 'Rejected; no accepted theorem; split or changed successor only')
 if a==14401:x.update(launcher_exit=67,disposition='Duplicate refusal: old 14400 barrier rejection consumed source/deps tuple. No Lean execution. Split smaller opening-value/query modules14402/14403; no ledger edit or bypass.')
 (e/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n');rows.append({k:x[k] for k in ['attempt','module','exit_status','source_sha256','print_axioms','errors','time_log']})
(e/'lean-summary.json').write_text(json.dumps(dict(attempts=rows,compiles=sum(z['exit_status'] is not None for z in rows),passed=sum(z['exit_status']==0 for z in rows),root_premises_removed=0),indent=2)+'\n')
print('accepted',sum(z['exit_status']==0 for z in rows),'compiles',sum(z['exit_status'] is not None for z in rows))
