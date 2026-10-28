from pathlib import Path
import subprocess,time,sys,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2c-20261028'
p=E/'lean-60538/receipt.json'
while not p.exists():time.sleep(5)
assert json.loads(p.read_text())['exit']==0
commands=[('scope.py','constructor-binding','complete constructor loop/call binding','python3','/home/dombarker/project-offloads/codex-pv-rdb2c-20261028/bind-constructor.py'),('scope.py','native-weights','optimized compile then 15 finite request traces and MIR lowering dump','python3','/home/dombarker/project-offloads/codex-pv-rdb2c-20261028/native-weights.py'),('queue.py','materialize-new.json','60539')]
for args in commands:
 for retry in range(11):
  r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2c-20261028'/args[0]),*args[1:]])
  if r.returncode==78 and retry<10:print('refusal cooldown 180 seconds',flush=True);time.sleep(180);continue
  break
 if r.returncode:sys.exit(r.returncode)
