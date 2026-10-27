from pathlib import Path
import json,sys
from RPv_attempt import E,R,B,run,ssh
p=json.loads((E/'RPv_plan.json').read_text())
def receipts():return [json.loads(f.read_text()) for f in E.glob('RPv_*/receipt.json')]
if __name__=='__main__':
 root=sys.argv[1];assert root in p['roots'];selected=set(p['closures'][root]);state={d['module']:d['exit_status']==0 for d in receipts()}
 r=ssh(f'mkdir -p {B}/RPv_overlay');assert r.returncode==0,r.stderr
 for row in p['rows']:
  if row['original'] not in selected or row['module'] in state:continue
  if len(receipts())>=1100:raise SystemExit('STOP budget exhausted')
  blocked=[i for i in row['imports'] if i.startswith('RPv_') and not state.get(i,False)]
  if blocked:
   with (E/'RPv_blocked.jsonl').open('a') as f:f.write(json.dumps(dict(module=row['module'],blocked=blocked))+'\n')
   continue
  d=run(f'RPv_{len(receipts())+1:04d}',row['module'],R/row['source'],row['imports']);state[row['module']]=d['exit_status']==0
  (E/'RPv_state.json').write_text(json.dumps(state,indent=2)+'\n')
