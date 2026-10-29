from pathlib import Path
import json,subprocess,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');R=D/'resume17';p=R/'project-resolution-resume17.json';x=json.loads(p.read_text());x['revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for m in sys.argv[1:]:
 q=D/'lean'/(m+'.lean');k='HEAD:'+str(q);b=q.read_bytes();assert subprocess.check_output(['git','show',k])==b
 x['modules'][m]=dict(module=m,path=str(q),blob=subprocess.check_output(['git','rev-parse',k],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),authority='h5 HEAD',imports=[l.split()[1]for l in b.decode().splitlines()if l.startswith('import ')],tracked_conflicts=[])
p.write_text(json.dumps(x,indent=2)+'\n')
