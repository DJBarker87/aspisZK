"""Serial harness queue; retries only unlaunched admission refusals."""
from pathlib import Path
import json,subprocess,time,sys
from run import H
for id,harness in json.loads((H/'resume16/queue.json').read_text()):
 for retry in range(11):
  cooldown=H/'admission-not-before.json'
  while cooldown.exists() and (remaining:=json.loads(cooldown.read_text())['epoch']-time.time())>0:
   print(json.dumps(dict(waiting_for_admission=True,seconds=round(remaining),id=id)),flush=True);time.sleep(min(30,remaining))
  r=subprocess.run(['python3',str(H/'kani227_resume16_host.py'),str(id),harness,'leaf'],stdout=(H/'resume16'/f'queue-{id}.log').open('w'),stderr=subprocess.STDOUT)
  print(json.dumps(dict(id=id,harness=harness,exit=r.returncode)),flush=True)
  if r.returncode!=78:break
 else:raise SystemExit('10 admission retries exhausted')
 # Continue independent cases after a failure; no unchanged failed harness rerun.
