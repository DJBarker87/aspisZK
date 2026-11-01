"""One focused scope at a time; never resubmit a failed source or refusal."""
from run import H
import subprocess,json
queue=['PV_B3P_DigestSource547227']+[f'PV_B3P_PathCell15_{i}227' for i in range(7,-1,-1)]+['PV_B3P_NativePath15227','PV_B3P_PathSource547227']
for module in queue:
 t=json.loads((H/'TALLY-resume18.json').read_text())
 if any(r['module']==module and r['exit']==0 for r in t.get('receipts',[])):continue
 r=subprocess.run(['python3',str(H/'compile_resume18.py'),module])
 if r.returncode:raise SystemExit(r.returncode)
