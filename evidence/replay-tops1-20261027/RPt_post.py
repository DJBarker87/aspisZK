from pathlib import Path
import json,sys
from RPt_attempt import E,R,run
rs=lambda:sorted([json.loads(f.read_text()) for f in E.glob('RPt_*/receipt.json')],key=lambda d:int(d['attempt'].split('_')[1]))
def execute(module,imports):
 receipts=rs()
 if any(d['module']==module for d in receipts):return
 a=len(receipts)+1;assert a<=400
 d=run(f'RPt_{a:03d}',module,E/(module+'.lean'),imports);assert d['exit_status']==0,d['attempt']
if sys.argv[1]=='ben':execute('RPt_BEnAudit',['Init','Lean','RPt_BEn_Top','RPz8_ARX_Root'])
elif sys.argv[1]=='batches':
 plan=json.loads((E/'RPt_plan.json').read_text());wanted={r['module'] for r in plan['rows']}
 passed=[d['module'] for d in rs() if d['exit_status']==0 and d['module'] in wanted]
 groups=[passed[i:i+100] for i in range(0,len(passed),100)]
 (E/'RPt_audit-groups.json').write_text(json.dumps(groups,indent=2)+'\n')
 for i,ms in enumerate(groups):
  module=f'RPt_AuditBatch{i+1:02d}'
  template=(R/'evidence/replay-dry9-20261027/RPz8_audit-template.txt').read_text().replace('RPZ8_','RPT_')
  # Retain predecessor's exact known syntax correction (RPz8_659).
  text=template.replace('@@IMPORTS@@','\n'.join('import '+m for m in ms)).replace('@@SELECTED@@','#[ '+', '.join('`'+m for m in ms)+' ]')
  (E/(module+'.lean')).write_text(text)
  execute(module,['Init','Lean']+ms)
else:raise SystemExit('ben|batches')
