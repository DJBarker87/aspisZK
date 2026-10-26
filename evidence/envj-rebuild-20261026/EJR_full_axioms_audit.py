"""Audit complete multiline #print axioms output; never launch Lean."""
from pathlib import Path
import json,re
O=Path(__file__).parent;P=O/'receipts/EJR_attempts.jsonl';rs=[json.loads(l) for l in P.read_text().splitlines()];bad=[]
for r in rs:
 out=(O/'receipts'/f'out-{r["attempt"]}.log').read_text();unsupported=[]
 for deps in re.findall(r'depends on axioms:\s*\[([^]]*)\]',out,re.S):
  unsupported.extend(sorted(set(deps.replace(',',' ').split())-{'propext','Classical.choice','Quot.sound'}))
 r['lean_exit']=int(re.search(r'Exit status:\s*(\d+)',r['time_log'])[1]);r['unsupported_printed_axioms']=sorted(set(unsupported))
 if r['lean_exit']==0 and unsupported:
  bad.append(dict(key=r['key'],attempt=r['attempt'],unsupported=r['unsupported_printed_axioms'],source_sha256=r['source_sha256'],object_sha256=r['object_sha256']));r['exit']=90;r['validation_exit']=90;r['audit_note']='Compiler succeeded; full standard-axioms audit failed. Preserve artifact as legacy evidence, exclude from approved validation.'
 else:r['validation_exit']=r['exit']
P.write_text(''.join(json.dumps(r)+'\n' for r in rs))
report=dict(allowed=['propext','Classical.choice','Quot.sound'],compiler_successes=sum(r['lean_exit']==0 for r in rs),standard_gate_passes=sum(r['exit']==0 for r in rs),standard_gate_failures=sum(r['exit']!=0 for r in rs),legacy_nonstandard=bad,new_top='R1Z.EJR_Verification.successor_nonzero',new_top_axioms=['propext'],note='Two historical modules depend on archived Aeneas core.fmt.Formatter : Type axiom. No profile rewrite or replay after budget exhaustion. No security release claim.')
(O/'EJR_full-axioms-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
