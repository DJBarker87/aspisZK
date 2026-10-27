"""Continue the four remaining independent probes serially after the first scope exits."""
from pathlib import Path
import subprocess,time,sys,json
E=Path(__file__).resolve().parent
while not (E/'XRh_006/receipt.json').exists():time.sleep(5)
for i in range(7,11):
 c=f'XRh_{i:03}.json';print('START',c,flush=True)
 subprocess.run([sys.executable,str(E/'XRh_launch.py'),c],check=True)
 r=json.loads((E/f'XRh_{i:03}/receipt.json').read_text());print('DONE',r['attempt'],r['exit_status'],flush=True)
 if r['exit_status'] in [124,137]:
  print('Resource/timeout stop: review before continuing independent scopes',flush=True);break
