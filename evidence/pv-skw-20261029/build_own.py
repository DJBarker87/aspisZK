from pathlib import Path
import json,subprocess,sys
D=Path('/home/dombarker/project-offloads/codex-pv-skw-20261029')
for n,r in enumerate(json.loads((D/'own-plan.json').read_text())['build'],68705):
 assert n<68797
 rc=subprocess.run(['python3',str(D/'run.py'),'lean'+str(n),'lean',str(n),r['module']])
 if rc.returncode:sys.exit(rc.returncode)
