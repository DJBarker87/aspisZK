"""Finish once the serial queue has completed039; never resubmit a scope."""
from pathlib import Path
import json,subprocess,sys,time
E=Path(__file__).resolve().parent
p=E/'NMQ_L039/receipt.json'
while not p.exists():time.sleep(5)
assert json.loads(p.read_text())['exit_status']==0,'Scan failed: no promotion or final scope'
while(E/'NMQ_CLIENT_ACTIVE').exists():time.sleep(1)
assert not(E/'NMQ_L040').exists()and not(E/'NMQ_L040.json').exists(),'Never resubmit040; recover read-only'
r=subprocess.run([sys.executable,str(E/'NMQ_run.py'),'NMQ_L040','audit','close'],capture_output=True,text=True)
(E/'NMQ_L040-client.log').write_text(r.stdout+r.stderr)
if r.returncode:print('STOP040: inspect retained receipt; never rerun unchanged',flush=True);sys.exit(r.returncode)
print('NMQ_L040 pin/retention PASS',flush=True)
for script in ['NMQ_provenance.py','NMQ_finalize.py','NMQ_hygiene.py','NMQ_validate.py','NMQ_deliver.py']:
 r=subprocess.run([sys.executable,str(E/script)],capture_output=True,text=True)
 (E/(script[:-3]+'-final.log')).write_text(r.stdout+r.stderr)
 if r.returncode:print('STOP metadata '+script+': '+(r.stdout+r.stderr)[-1200:],flush=True);sys.exit(r.returncode)
 print(script+' PASS',flush=True)
print('NMQ complete; final commit pending',flush=True)
