from pathlib import Path
import time,subprocess,sys,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2c-20261028';p=E/'lean-60583/receipt.json'
while not p.exists():time.sleep(5)
assert json.loads(p.read_text())['exit']==0
commands=[('scope.py','box-llvm-fixed','optimized diagnostic emission for missing Box intrinsic-lowering artifact','python3','/home/dombarker/project-offloads/codex-pv-rdb2c-20261028/llvm-box.py'),('scope.py','native-v239','optimized varying-column finite validation','python3','/home/dombarker/project-offloads/codex-pv-rdb2c-20261028/native-v239.py'),('queue.py','post-reserve.json','60584')]
for args in commands:
 for retry in range(11):
  r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2c-20261028'/args[0]),*args[1:]])
  if r.returncode==78 and retry<10:print('refusal cooldown 180 seconds',flush=True);time.sleep(180);continue
  break
 if r.returncode:sys.exit(r.returncode)
