from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag6-20261029')
for i,r in enumerate(json.loads((D/'inherited-sources.json').read_text())):
 assert hashlib.sha256((D/'sources'/(r['module']+'.lean')).read_bytes()).hexdigest()==r['sha256']
 n=65200+i
 p=subprocess.run(['python3',str(D/'run.py'),'lean'+str(n),'lean',str(n),r['module']])
 if p.returncode:raise SystemExit(p.returncode)
