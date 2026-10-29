from pathlib import Path
import json,subprocess,sys
D=Path('/home/dombarker/project-offloads/codex-pv-diag12-20261029')
plans=json.loads((D/'plans.json').read_text())
for idx in map(int,sys.argv[1:]):
 p=plans[idx];(D/'sources'/(p['module']+'.lean')).write_text(p['source'])
 n=max([int(f.name[4:9]) for f in D.glob('lean*-receipt.json')]+[67299])+1;assert n<67397
 r=subprocess.run(['python3',str(D/'run.py'),'lean'+str(n),'lean',str(n),p['module']],capture_output=True,text=True)
 print(idx,n,p['module'],r.returncode, r.stdout[-5500:] if r.returncode else '',flush=True)
 if r.returncode:sys.exit(r.returncode)
