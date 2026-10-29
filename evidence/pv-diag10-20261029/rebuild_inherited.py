from pathlib import Path
import subprocess,hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-diag10-20261029');P=D.parent/'codex-pv-diag9-20261029'
names=['Result','Frames','Operands','World','Retry','Honest','Scope','Encoders','Handoff']
rows=[]
for n,name in enumerate(names,66706):
 m='PV_DIAG9_'+name;p=P/'sources'/(m+'.lean');data=p.read_bytes()
 accepted=[json.loads(q.read_text()) for q in P.glob('lean*-receipt.json')]
 digest=hashlib.sha256(data).hexdigest();assert any(r.get('exit')==0 and r.get('module')==m and r.get('source_sha256')==digest for r in accepted)
 (D/'sources'/(m+'.lean')).write_bytes(data)
 p=subprocess.run(['python3',str(D/'run.py'),'lean'+str(n),'lean',str(n),m])
 rows.append(dict(module=m,attempt=n,source_sha256=digest,exit=p.returncode))
 (D/'inherited-rebuild.json').write_text(json.dumps(rows,indent=2)+'\n')
 if p.returncode:raise SystemExit(p.returncode)
