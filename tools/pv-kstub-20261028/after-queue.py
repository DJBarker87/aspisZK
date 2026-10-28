"""Continue strictly serially after the outstanding queue has returned its last result."""
from pathlib import Path
import time,subprocess,sys,os
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028'
while not (E/'K29-result.json').exists():
 try:os.kill(75111,0)
 except ProcessLookupError:sys.exit('Queue stopped before K29; review its output before continuing')
 time.sleep(15)
time.sleep(5)
for script in ['final-control.py','collect-sources.py','continue-lean.py','summarize.py','validate.py']:
 print('Serial next:',script,flush=True)
 q=subprocess.run([sys.executable,str(R/'tools/pv-kstub-20261028'/script)])
 if q.returncode:sys.exit(q.returncode)
