"""Sequential focused targets, with full recorded cooldowns and same-ID retries."""
from run import H
from pathlib import Path
import subprocess,json,time,hashlib
queue=['PV_B3P_ExternalSumsDefs554227','PV_B3P_ExternalSums554227','PV_B3P_ExternalAdd554227','PV_B3P_ExpandSource554227','PV_B3P_ConstructorSource554227','PV_B3P_ExternalSource554227']
for module in queue:
 refusals=0
 while True:
  t=json.loads((H/'TALLY-resume18.json').read_text())
  sha=hashlib.sha256((H/'lean'/(module+'.lean')).read_bytes()).hexdigest()
  if any(r.get('module')==module and r.get('exit_status')==0 and r.get('source_sha256')==sha for p in H.glob('lean-*/receipt/receipt.json') for r in [json.loads(p.read_text())]):break
  until=json.loads((H/'admission-not-before.json').read_text())['epoch'] if (H/'admission-not-before.json').exists() else 0
  while time.time()<until:
   wait=min(60,until-time.time());print(json.dumps(dict(module=module,cooldown_seconds=round(until-time.time(),1))),flush=True);time.sleep(wait)
  retry=next((r['attempt']for r in reversed(t.get('refusals',[])) if r['module']==module and r['attempt'] not in [79010,79011,79029,79074] and not any(x['attempt']==r['attempt']for x in t.get('receipts',[]))),None)
  cmd=['python3',str(H/'compile_resume18_extended.py'),module]+([f'--retry-admission={retry}'] if retry else [])
  r=subprocess.run(cmd)
  if r.returncode==78:
   refusals+=1
   if refusals>=10:raise SystemExit('ten reservation refusals; do compile-free work and return to queue')
   continue
  if r.returncode:raise SystemExit(r.returncode)
  break
print('focused queue complete',flush=True)
