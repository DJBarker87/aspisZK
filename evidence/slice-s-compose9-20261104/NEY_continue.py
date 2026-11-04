"""Sequential job-owned continuation; no shared launcher/monitor changes."""
from pathlib import Path
import subprocess,sys,time,json,datetime
E=Path(__file__).resolve().parent
last=0
while not (E/'NEY_K052/receipt.json').exists() or (E/'NEY_ACTIVE.json').exists():
 if time.time()-last>=1800:
  branches=subprocess.check_output(['git','branch','--list','*slice-s-leaves*'],text=True)
  entry=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),branches=branches,credit='read-only check; no unvalidated import')
  if branches.strip():entry['log']=subprocess.check_output(['git','log','-5','--oneline',branches.strip().splitlines()[0].strip()],text=True)
  with (E/'NEY_NEC_CHECKS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
  last=time.time()
 time.sleep(5)
subprocess.run([sys.executable,str(E/'NEY_public_campaign.py')],check=True)
subprocess.run([sys.executable,str(E/'NEY_remaining_campaign.py')],check=True)
