from run import H
import json,time,subprocess
R=H/'resume17'
while not any(R.glob('N73925*/receipt/receipt.json')):time.sleep(15)
for i,g in enumerate(['host-mask','statement-mask','reconstruct','transition','external','internal']):
 for retry in range(11):
  p=H/'admission-not-before.json'
  while p.exists()and(left:=json.loads(p.read_text())['epoch']-time.time())>0:time.sleep(min(30,left))
  with (R/f'std-stage-{g}-{retry}.log').open('w')as f:s=subprocess.run(['python3','std227_resume17_host.py',g,str(73960+i)],cwd=H,stdout=f,stderr=subprocess.STDOUT).returncode
  print(json.dumps(dict(group=g,exit=s,retry=retry)),flush=True)
  if s!=78:break
 else:raise SystemExit('admission retries exhausted')
