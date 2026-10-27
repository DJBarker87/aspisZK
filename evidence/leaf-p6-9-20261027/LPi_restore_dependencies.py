"""Build only missing unchanged LPf objects, privately and serially."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for number,module in enumerate(json.loads((E/'LPi_LPf_missing.json').read_text()),29):
 a=f'LPi_L{number:03d}'
 r=subprocess.run([sys.executable,str(E/'LPi_lean.py'),a,'lean/'+module+'.lean',module],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(r.stdout[-900:],flush=True)
 if r.returncode:raise SystemExit('STOP launcher failure '+a)
 rc=json.loads((E/a/'receipt.json').read_text())
 if rc['exit_status']!=0:raise SystemExit('STOP dependency nonpass '+a)
