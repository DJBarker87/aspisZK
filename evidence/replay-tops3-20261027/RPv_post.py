from pathlib import Path
import json,sys
from RPv_attempt import E,R,run
p=json.loads((E/'RPv_plan.json').read_text())
def receipts():return sorted([json.loads(f.read_text()) for f in E.glob('RPv_*/receipt.json')],key=lambda d:d['attempt'])
def execute(m,imports):
 rs=receipts()
 if any(d['module']==m for d in rs):return
 assert len(rs)<1100
 d=run(f'RPv_{len(rs)+1:04d}',m,E/(m+'.lean'),imports);assert d['exit_status']==0,d['attempt']
if __name__=='__main__':
 root=sys.argv[1];assert root in p['roots'];execute('RPv_'+root+'Audit',['Init','Lean','RPv_'+root])
 passed={d['module'] for d in receipts() if d['exit_status']==0};old=json.loads((E/'RPv_audit-groups.json').read_text()) if (E/'RPv_audit-groups.json').exists() else [];covered={m for g in old for m in g};ms=[r['module'] for r in p['rows'] if r['module'] in passed and r['module'] not in covered];groups=old+[ms[i:i+100] for i in range(0,len(ms),100)];(E/'RPv_audit-groups.json').write_text(json.dumps(groups,indent=2)+'\n')
 for i,group in enumerate(groups):
  m=f'RPv_AuditBatch{i+1:02d}';template=(R/'evidence/replay-dry9-20261027/RPz8_audit-template.txt').read_text().replace('RPZ8_','RPV_');text=template.replace('@@IMPORTS@@','\n'.join('import '+m for m in group)).replace('@@SELECTED@@','#[ '+', '.join('`'+m for m in group)+' ]');(E/(m+'.lean')).write_text(text);execute(m,['Init','Lean']+group)
