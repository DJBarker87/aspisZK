from pathlib import Path
import json,sys
from RPu_attempt import E,R,B,run,ssh
p=json.loads((E/'RPu_plan.json').read_text());rs=lambda:sorted([json.loads(f.read_text()) for f in E.glob('RPu_*/receipt.json')],key=lambda d:int(d['attempt'].split('_')[1]))
if __name__=='__main__':
 state={d['module']:d['exit_status']==0 for d in rs()}
 r=ssh(f'mkdir -p {B}/RPu_overlay');assert r.returncode==0,r.stderr
 cap=int(sys.argv[1]);assert cap<=495
 # Dependency postorder visits FJp, FJu, then FJv_Top and Deployed.
 for row in p['rows']:
  if row['module'] in state:continue
  if len(rs())>=cap:break
  assert all(i not in state or state[i] for i in row['imports'])
  d=run(f'RPu_{len(rs())+1:03d}',row['module'],R/row['source'],row['imports'])
  state[row['module']]=d['exit_status']==0
  (E/'RPu_state.json').write_text(json.dumps(state,indent=2)+'\n')
  if not state[row['module']]:raise SystemExit('STOP source chain '+row['module'])
