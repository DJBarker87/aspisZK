"""Serial execution of already-prepared focused commands, no launcher changes."""
from pathlib import Path
from run import H
import time,json,subprocess
R=H/'resume17'
while not (R/'N73917/receipt/receipt.json').exists():time.sleep(15)
commands=[['python3','compile_resume17.py','PV_B3P_DirectAbsorption17227']]
commands += [['python3','direct_group227_resume17_host.py',g,str(n)] for g,n in [('copy',73918),('field',73919),('poseidon',73920),('statement-copy',73921)]]
for i,cmd in enumerate(commands):
 for retry in range(11):
  cooldown=H/'admission-not-before.json'
  while cooldown.exists()and (left:=json.loads(cooldown.read_text())['epoch']-time.time())>0:time.sleep(min(30,left))
  with (R/f'continue-{i}-{retry}.log').open('w')as f:status=subprocess.run(cmd,cwd=H,stdout=f,stderr=subprocess.STDOUT).returncode
  print(json.dumps(dict(command=cmd,exit=status,retry=retry)),flush=True)
  if status!=78:break
 else:raise SystemExit('admission attempts exhausted')
