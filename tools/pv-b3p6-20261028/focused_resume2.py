"""Sequential focused modules; required cooldown before next-ID admission retry."""
from pathlib import Path
import json,subprocess,sys,time
from run import H
for module in sys.argv[1:]:
 for retry in range(11):
  p=H/'admission-not-before.json'
  while p.exists():
   delay=json.loads(p.read_text())['epoch']-time.time()
   if delay<=0:break
   print(json.dumps(dict(module=module,cooldown_seconds=round(delay),retry=retry)),flush=True)
   time.sleep(min(60,delay+0.1))
  r=subprocess.run(['python3',str(H/'compile_resume2.py'),module])
  if r.returncode==0:break
  if r.returncode!=78 or retry==10:sys.exit(r.returncode)
 else:raise AssertionError('unreachable')
