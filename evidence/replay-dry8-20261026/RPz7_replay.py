"""Serial critical-path replay using the retained S2W launcher and job view."""
from pathlib import Path
import json,math
from RPz7_attempt import run,E,R
p=json.loads((E/'RPz7_plan.json').read_text());rows=p['rows'];mapping=p['mapping']
state={m:'passed' for m in p['reuse']};state['S1SemanticPhaseV1']='passed';attempt=2
for f in sorted(E.glob('RPz7_*/receipt.json')):
 d=json.loads(f.read_text());attempt=max(attempt,int(d['attempt'].split('_')[1]))
 orig=next((r['original'] for r in rows if r['module']==d['module']),None)
 if orig:state[orig]='passed' if d['exit_status']==0 else 'failed'
# Existing order is dependency-topological, traversed from Rc10's actual imports.
# Prioritise the S1 carrier's immediate body before the rest of the top closure.
priority=['S1SemanticPrefixModelV1','S1SemanticFinishModelV1','S1SemanticVerifyReachabilityV1','S1SemanticCodeFinishV1','S1SemanticCodeVerifyV1']
lookup={r['original']:r for r in rows}
original_plan=json.loads((R/'evidence/replay-dry6-20261026/RPz5_source-plan.json').read_text())
while attempt<1478:
 ready=[m for m in p['order'] if m in lookup and m not in state and all(n not in mapping or state.get(n)=='passed' for n in original_plan['modules'][m]['imports'])]
 if not ready:break
 m=next((m for m in priority if m in ready),ready[0]);row=lookup[m];attempt+=1
 d=run(f'RPz7_{attempt:03d}',row['module'],R/row['source'],row['imports'])
 state[m]='passed' if d['exit_status']==0 else 'failed'
 (E/'RPz7_state.json').write_text(json.dumps({'attempts':attempt,'state':state},indent=2)+'\n')
 if d['exit_status'] in [124,137]:print('STOP killed/timed-out source; isolate before further dependent work',flush=True);break
print('SOURCE STAGE',attempt,'passed',sum(s=='passed' for s in state.values()),'failed',sum(s=='failed' for s in state.values()),flush=True)
