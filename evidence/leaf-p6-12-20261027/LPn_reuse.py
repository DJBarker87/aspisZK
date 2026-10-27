"""Build only missing unchanged imported modules, serially; no proof changes."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
for i,module in enumerate(json.loads((E/'LPn_reuse-plan.json').read_text()),1):
 a=f'LPn_L{i:03}'
 subprocess.run(['python3',str(E/'LPn_attempt.py'),a,'reuse',module],check=True,stdout=(E/(a+'-summary.log')).open('w'),stderr=subprocess.STDOUT)
 r=json.loads((E/a/'receipt.json').read_text())
 print(a,module,r['exit_status'],flush=True)
 if r['exit_status']:raise SystemExit('STOP prerequisite error')
