"""Serial invocation of existing job tools, respecting each recorded cooldown.
No launcher, reservation, cap, shared source, or shared object is modified.
"""
from run import H
from pathlib import Path
import json,time,subprocess,sys

def invoke(cmd):
 for retry in range(11):
  p=H/'admission-not-before.json'
  while p.exists() and (remaining:=json.loads(p.read_text())['epoch']-time.time())>0:
   time.sleep(min(30,remaining))
  r=subprocess.run(cmd,cwd=H)
  if r.returncode!=78:return r.returncode
  print(json.dumps(dict(refused=cmd,retry=retry,cooldown='full180 seconds; next invocation checks current admission again')),flush=True)
 return 78

for module in ['PV_B3P_Resume9Combined','PV_B3P_Resume9Axioms','PV_B3P_Resume9Focused']:
 r=invoke(['python3','compile_resume9.py',module,'audit'])
 if r:raise SystemExit(r)
