"""Serial replay of only the inherited unbuilt dependency frontier."""
import json
from RPz8_attempt import E,R,run,ssh,B
p=json.loads((E/'RPz8_plan.json').read_text());rows={r['original']:r for r in p['rows']};rev={r['module']:r['original'] for r in p['rows']};state={};attempt=0
for f in sorted(E.glob('RPz8_*/receipt.json')):
 d=json.loads(f.read_text());attempt=max(attempt,int(d['attempt'].split('_')[1]));m=rev.get(d['module'])
 if m:state[m]='passed' if d['exit_status']==0 else 'failed'
r=ssh(f'mkdir -p {B}/RPz8_overlay');assert r.returncode==0,r.stderr
while attempt<1500:
 ready=[m for m in p['order'] if m not in state and all(n not in rev or state.get(rev[n])=='passed' for n in rows[m]['imports'])]
 if not ready:break
 m=ready[0];r=rows[m];attempt+=1
 d=run(f'RPz8_{attempt:03d}',r['module'],R/r['source'],r['imports'])
 state[m]='passed' if d['exit_status']==0 else 'failed'
 (E/'RPz8_state.json').write_text(json.dumps({'attempts':attempt,'state':state},indent=2)+'\n')
print('SOURCE FRONTIER',attempt,'passed',sum(v=='passed' for v in state.values()),'failed',sum(v=='failed' for v in state.values()),'unbuilt',len(rows)-len(state),flush=True)
