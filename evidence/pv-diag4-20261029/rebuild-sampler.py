from pathlib import Path
import json,subprocess,sys
D=Path('/home/dombarker/project-offloads/codex-pv-diag4-20261029');plan=json.loads((D/'sampler-rebuild-plan.json').read_text())
remaining=[m for m in plan['order'] if not any(json.loads(p.read_text()).get('module')==m and json.loads(p.read_text()).get('exit')==0 for p in D.glob('lean*-receipt.json'))]
for i,m in enumerate(remaining,64521):
 p=subprocess.run(['python3',str(D/'run.py'),f'lean{i}','lean',str(i),m]);
 if p.returncode:sys.exit(p.returncode)
