from run import H
import json,time,subprocess
R=H/'resume17'
commands=[['python3','compile_resume17.py','PV_B3P_DirectAbsorption17227']]+[['python3','direct_group227_resume17_host.py',g,str(n)] for g,n in [('field-retry',73922),('poseidon-retry',73923),('statement-copy-retry',73924),('copy-methods',73925)]]
for i,cmd in enumerate(commands):
 for retry in range(11):
  p=H/'admission-not-before.json'
  while p.exists()and(left:=json.loads(p.read_text())['epoch']-time.time())>0:time.sleep(min(30,left))
  with (R/f'retry-{i}-{retry}.log').open('w')as f:s=subprocess.run(cmd,cwd=H,stdout=f,stderr=subprocess.STDOUT).returncode
  print(json.dumps(dict(command=cmd,exit=s,retry=retry)),flush=True)
  if s!=78:break
 else:raise SystemExit('admission retries exhausted')
