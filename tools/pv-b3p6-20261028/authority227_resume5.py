"""Resolve only this resume's explicit, HEAD-tracked proof modules (h5)."""
from pathlib import Path
import json,hashlib,subprocess,sys
D=Path('evidence/pv-b3p6-20261028');p=D/'project-resolution-resume5.json';x=json.loads(p.read_text());revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for module in sys.argv[1:]:
 assert module.startswith('PV_B3P_') and '.'not in module
 q=D/'lean'/(module+'.lean');data=q.read_bytes();key='HEAD:'+str(q);assert subprocess.check_output(['git','show',key])==data
 x['modules'][module]=dict(module=module,path=str(q),blob=subprocess.check_output(['git','rev-parse',key],text=True).strip(),sha256=hashlib.sha256(data).hexdigest(),authority='h5 HEAD',imports=[l.split()[1]for l in data.decode().splitlines()if l.startswith('import ')],tracked_conflicts=[])
x['revision']=revision;p.write_text(json.dumps(x,indent=2)+'\n');(D/'resume5-proof-revision.txt').write_text(revision+'\n')
