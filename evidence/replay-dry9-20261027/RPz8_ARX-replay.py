"""Candidate-root continuation; invoke only after original frontier dispatch ends."""
import json
from RPz8_attempt import E,R,run
p=json.loads((E/'RPz8_ARX-plan.json').read_text());rows={r['module']:r for r in p['rows']};state={};attempt=0
allrows={r['module']:r for name in ['RPz8_plan.json','RPz8_ARX-plan.json'] for r in json.loads((E/name).read_text())['rows']}
for f in sorted(E.glob('RPz8_*/receipt.json')):
 d=json.loads(f.read_text());attempt=max(attempt,int(d['attempt'].split('_')[1]));state[d['module']]='passed' if d['exit_status']==0 else 'failed'
while attempt<1500:
 ready=[r for r in p['rows'] if r['module'] not in state and all(n not in allrows or state.get(n)=='passed' for n in r['imports'])]
 if not ready:break
 r=ready[0];attempt+=1;d=run(f'RPz8_{attempt:03d}',r['module'],R/r['source'],r['imports']);state[r['module']]='passed' if d['exit_status']==0 else 'failed'
 (E/'RPz8_ARX-state.json').write_text(json.dumps({'attempts':attempt,'state':{m:s for m,s in state.items() if m in rows}},indent=2)+'\n')
print('ARX FRONTIER',attempt,'passed',sum(state.get(m)=='passed' for m in rows),'failed',sum(state.get(m)=='failed' for m in rows),'unbuilt',sum(m not in state for m in rows),flush=True)
