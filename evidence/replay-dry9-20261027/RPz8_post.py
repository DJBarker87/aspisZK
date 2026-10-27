"""Serial fresh-root queries and batched declaration audits; never import failed modules."""
import json,sys
from RPz8_attempt import E,R,run
receipts=lambda:sorted([json.loads(f.read_text()) for f in E.glob('RPz8_*/receipt.json')],key=lambda x:int(x['attempt'].split('_')[1]))
def next_attempt():return max(int(r['attempt'].split('_')[1]) for r in receipts())+1
if sys.argv[1]=='roots':
 passed={d['module'] for d in receipts() if d['exit_status']==0}
 for root in ['Rc10_Top','ARX_Root']:
  module='RPz8_'+root+'Audit'
  if 'RPz8_'+root not in passed:print('SKIP root audit: source not green',root,flush=True);continue
  if any(d['module']==module for d in receipts()):continue
  a=next_attempt();assert a<=1500
  d=run(f'RPz8_{a:03d}',module,E/(module+'.lean'),['Init','Lean','RPz8_'+root])
  if d['exit_status']!=0:print('STOP this root audit chain; changed-input isolation required',module,flush=True)
elif sys.argv[1]=='batches':
 plans=[json.loads((E/n).read_text()) for n in ['RPz8_plan.json','RPz8_ARX-plan.json']]
 wanted={r['module']:r for p in plans for r in p['rows']};passed=[d['module'] for d in receipts() if d['exit_status']==0 and d['module'] in wanted]
 # Fixed partitions are receipt-pinned and resumed without repeated compiles.
 groups=[passed[i:i+100] for i in range(0,len(passed),100)]
 (E/'RPz8_audit-groups.json').write_text(json.dumps(groups,indent=2)+'\n')
 for i,ms in enumerate(groups):
  module=f'RPz8_AuditBatch{i+1:02d}'
  prior=next((d for d in receipts() if d['module']==module),None)
  if prior and prior['exit_status']!=0:module+='Fixed'
  if any(d['module']==module for d in receipts()):continue
  t=(E/'RPz8_audit-template.txt').read_text().replace('@@IMPORTS@@','\n'.join('import '+m for m in ms)).replace('@@SELECTED@@','#[ '+', '.join('`'+m for m in ms)+' ]');src=E/(module+'.lean');src.write_text(t)
  a=next_attempt();assert a<=1500;d=run(f'RPz8_{a:03d}',module,src,['Init','Lean']+ms)
  if d['exit_status']!=0:print('STOP failed audit partition',module,flush=True);break
else:raise SystemExit('roots|batches')
