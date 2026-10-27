import json,sys
from RPx_attempt import E,R,B,run,ssh
p=json.loads((E/'RPx_plan.json').read_text())
if __name__=='__main__':
 stop=sys.argv[1] if len(sys.argv)>1 else None
 r=ssh(f'mkdir -p {B}/RPx_overlay');assert r.returncode==0,r.stderr
 receipts=[json.loads(f.read_text()) for f in E.glob('RPx_*/receipt.json')]
 state={d['module']:d['exit_status']==0 for d in receipts};fresh={r['module'] for r in p['rows']}
 for row in p['rows']:
  if row['module'] in state:
   assert state[row['module']], 'failed source requires isolation before retry'
   if stop==row['module']:break
   continue
  assert len(receipts)<150,'budget exhausted'
  assert all(i not in fresh or state.get(i,False) for i in row['imports']),row
  d=run(f'RPx_{len(receipts)+1:04d}',row['module'],R/row['source'],['Init']+row['imports']);receipts.append(d)
  assert d['exit_status']==0,d
  state[row['module']]=True
  if stop==row['module']:break
