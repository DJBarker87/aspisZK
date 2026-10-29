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

if sys.argv[1]=='llvm':raise SystemExit(invoke(['python3','llvm227_resume14_host.py']))
order=sys.argv[2:] if sys.argv[1]=='modules' else json.loads((H/'bootstrap.json').read_text())
for module in order:
 r=invoke(['python3','compile_resume14.py',module])
 if r:raise SystemExit(r)
