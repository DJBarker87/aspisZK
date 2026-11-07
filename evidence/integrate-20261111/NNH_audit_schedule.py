"""One capped raw-axiom group at a time; no inherited root is re-audited."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;groups=json.loads((E/'NNH_AUDIT_ROOTS.json').read_text())['groups']
for i in range(1,len(groups)):
 a=f'NNH_L{55+i:03}'
 r=subprocess.run(['python3',str(E/'NNH_run.py'),a,'audit','proof'+str(i)])
 if r.returncode:raise SystemExit(r.returncode)
