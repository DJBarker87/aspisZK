"""Read-only receipt collector for the resumed assigned range; never launches jobs."""
from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026'
rows=[]
for p in sorted(e.glob('13*-input.json')):
 x=json.loads(p.read_text());a=x['attempt'];s=e/f'{a}.lean.txt';assert hashlib.sha256(s.read_bytes()).hexdigest()==x['source_sha256']
 log=(e/f'out-{a}.log').read_text();t=(e/f'time-{a}.log').read_text() if (e/f'time-{a}.log').exists() else ''
 m=re.search(r'^exit=(\d+)',log,re.M);status=int(m[1]) if m else None
 reports=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)
 if status==0:
  assert 'sorryAx' not in log and 'error:' not in log
  for z in reports:
   if z.startswith("'Aeneas.Std.core.fmt.Formatter'"):
    assert x['module']=='R1Z/PDict_FormatterDiagnostic' and 'Aeneas.Std.core.fmt.Formatter]' in z
    continue
   if 'depends on axioms: [' in z: assert set(v.strip() for v in z.split('depends on axioms: [')[1][:-1].replace('\n','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
 x.update(diagnostic_only=x['module']=='R1Z/PDict_FormatterDiagnostic',exit_status=status,command=f"sh {x['launcher']} {a} {x['module']} J 7000 7 {x['deps_fingerprint']}",time_log=t,print_axioms=reports,errors=[z for z in log.splitlines() if 'error:' in z],disposition='Focused proof accepted; not frozen release replay' if status==0 else 'Rejected; changed successor required')
 (e/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n');rows.append({k:x[k] for k in ['attempt','module','exit_status','source_sha256','errors','print_axioms','time_log']})
(e/'resume/lean-summary.json').write_text(json.dumps(dict(attempts=rows,compiles=len(rows),remaining=67-len(rows),root_premises_removed=0),indent=2)+'\n')
print(len(rows),'resumed compile attempts')
