from pathlib import Path
import subprocess,time,sys,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2c-20261028'
p=E/'lean-60515/receipt.json'
while not p.exists():time.sleep(5)
assert json.loads(p.read_text())['exit']==0
for args in [('scope.py','alloc-binding-fixed','typed RawVec and Box/public allocation source checks','python3','/home/dombarker/project-offloads/codex-pv-rdb2c-20261028/bind-alloc.py'),('queue.py','new-first.json','60516'),('queue.py','weights-owned.json','60519')]:
 r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2c-20261028'/args[0]),*args[1:]])
 if r.returncode:sys.exit(r.returncode)
