"""Sequential bounded replay driver; one scope at a time."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;p=json.loads((E/'plan.json').read_text());cap=int(sys.argv[1]);assert cap<=40 or (E/'budget-extension.json').exists()
used=len(list(E.glob('lean-*/receipt.json')))
for m in p['build_order']:
 if any(json.loads(q.read_text()).get('module')==m and json.loads(q.read_text())['exit']==0 for q in E.glob('lean-*/receipt.json')):continue
 if used>=cap:print('BUDGET CAP',used,flush=True);break
 n={'R1Z.PV_RDB2F_StatementAudit':63997,'R1Z.PV_RDB2F_AxiomsAudit':63998,'R1Z.PV_RDB2F_FocusedReplay':63999}.get(m,63900+used)
 r=subprocess.run([sys.executable,str(E/'lean.py'),str(n),m]);
 if r.returncode:sys.exit(r.returncode)
 used+=1
