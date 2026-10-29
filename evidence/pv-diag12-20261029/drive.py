from pathlib import Path
import json,sys,subprocess,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag12-20261029')
plans=json.loads((D/'plans.json').read_text())
start=int(sys.argv[1]);end=int(sys.argv[2]) if len(sys.argv)>2 else len(plans)
for idx in range(start,end):
 p=plans[idx];src=D/'sources'/(p['module']+'.lean');src.write_text(p['source'])
 used=[int(f.name[4:9]) for f in D.glob('lean*-receipt.json')]
 n=max(used+[67299])+1;assert n<67397
 assert hashlib.sha256(src.read_bytes()).hexdigest()==p['sha256']
 print('STAGE',idx,n,p['module'],flush=True)
 run=subprocess.run(['python3',str(D/'run.py'),'lean'+str(n),'lean',str(n),p['module']],text=True,capture_output=True)
 rc=run.returncode
 print(run.stdout[-6000:] if rc else 'ACCEPTED '+str(n),flush=True)
 if rc:sys.exit(rc)
