from pathlib import Path
import json,subprocess,sys
D=Path('/home/dombarker/project-offloads/codex-pv-diag4-20261029');plan=json.loads((D/'sampler-rebuild-plan.json').read_text())
for i,m in enumerate(plan['order'][1:],64503):
 p=subprocess.run(['python3',str(D/'run.py'),f'lean{i}','lean',str(i),m]);
 if p.returncode:sys.exit(p.returncode)
