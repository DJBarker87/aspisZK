"""Select tracked diag2 laws for private replay; do not modify their source."""
from pathlib import Path
import json,hashlib,subprocess,re
E=Path('evidence/pv-l1d-20261029');pin=E/'focused-resolution.json';sp=E/'focused-project-sources.json'
x=json.loads(pin.read_text());ss=json.loads(sp.read_text());rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
mods=['PV_DIAG2_Retry','PV_DIAG2_Rejection','PV_DIAG2_ClientRetry']
for m in mods:
 p='evidence/pv-diag2-20261029/'+m+'.lean';b=subprocess.check_output(['git','show',rev+':'+p])
 x['resolved'][m]=dict(authority='h5 own git-tracked HEAD',path=p,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+p],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),imports=re.findall(r'^import (\S+)',b.decode(),re.M),tracked_conflicts=[])
 ss[m]=b.decode()
pin.write_text(json.dumps(x,indent=2)+'\n');sp.write_text(json.dumps(ss)+'\n')
p=E/'missing-order.json';xs=json.loads(p.read_text());p.write_text(json.dumps(xs+mods,indent=2)+'\n')
print('Selected three immutable diag2 laws for private recompilation')
