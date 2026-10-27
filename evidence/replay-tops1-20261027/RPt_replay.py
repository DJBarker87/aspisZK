from pathlib import Path
import json,sys
from RPt_attempt import E,R,B,T,run,ssh
p=json.loads((E/'RPt_plan.json').read_text()); rows={r['original']:r for r in p['rows']}
rs=lambda: sorted([json.loads(f.read_text()) for f in E.glob('RPt_*/receipt.json')],key=lambda d:int(d['attempt'].split('_')[1]))
if sys.argv[1]=='build':
 receipts=rs(); state={d['module']:d['exit_status']==0 for d in receipts}
 r=ssh(f'mkdir -p {B}/RPt_overlay');assert r.returncode==0,r.stderr
 # BEn closure first, then original dependency order. One scope, sequential.
 b=set(p['closures']['BEn_Top']);order=[r for r in p['rows'] if r['original'] in b]+[r for r in p['rows'] if r['original'] not in b]
 for row in order:
  if row['module'] in state:continue
  if any(i in state and not state[i] for i in row['imports']):continue
  a=len(rs())+1
  # Reserve four batch audit attempts for the completed BEn root and declaration batches.
  if a>396:break
  d=run(f'RPt_{a:03d}',row['module'],R/row['source'],row['imports']);state[row['module']]=d['exit_status']==0
  (E/'RPt_state.json').write_text(json.dumps(state,indent=2)+'\n')
  if not state[row['module']]:print('STOP source chain:',row['module'],flush=True);break
  if row['original']=='BEn_Top':break
