"""Collect immutable focused receipts; no workload or infrastructure changes."""
from pathlib import Path
import json,re,hashlib
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/continued'
rows=[]
for p in sorted(e.glob('136*-input.json')):
 x=json.loads(p.read_text());a=x['attempt'];assert hashlib.sha256((e/f'{a}.lean.txt').read_bytes()).hexdigest()==x['source_sha256']
 s=(e/f'out-{a}.log').read_text();t=(e/f'time-{a}.log').read_text();m=re.search(r'^exit=(\d+)',s,re.M);status=int(m[1]) if m else None
 reports=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",s)
 if status==0:
  assert 'sorryAx' not in s and 'error:' not in s
  for z in reports:
   if 'depends on axioms: [' in z:assert set(v.strip() for v in z.split('depends on axioms: [')[1][:-1].replace('\n','').split(','))<={'propext','Classical.choice','Quot.sound'}
 x.update(exit_status=status,command=f"sh {x['launcher']} {a} {x['module']} J 7000 7 {x['deps_fingerprint']}",time_log=t,print_axioms=reports,errors=[z for z in s.splitlines() if 'error:' in z],disposition='Accepted focused source/value proof, not a frozen release replay' if status==0 else 'Rejected; changed successor retained')
 (e/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n');rows.append({k:x[k] for k in ['attempt','module','exit_status','source_sha256','print_axioms','errors','time_log']})
(e/'lean-summary.json').write_text(json.dumps(dict(attempts=rows,compiles=len(rows),remaining=51-len(rows),root_premises_removed=0),indent=2)+'\n');print(len(rows),'attempts;',51-len(rows),'remain')
