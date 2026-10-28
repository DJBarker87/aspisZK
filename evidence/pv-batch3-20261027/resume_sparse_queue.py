"""Sequential focused proof queue. Refusals always wait >=180 s; next ID only."""
from pathlib import Path
import json,time,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
start=int(sys.argv[1]);already=int(sys.argv[2]) if len(sys.argv)>2 else 0
log=H/'resume-queue-events.jsonl'
def event(**e):
 e['epoch']=time.time()
 with log.open('a') as f:f.write(json.dumps(e)+'\n')
 print(json.dumps(e),flush=True)
for i in range(start,-1,-1):
 m=f'PV_B3_MaskSparse{i:02}';refusals=already if i==start else 0
 while True:
  cooldown=H/'admission-not-before.json'
  if cooldown.exists():
   until=json.loads(cooldown.read_text())['epoch']
   if time.time()<until:
    event(module=m,kind='cooldown_wait',not_before=until)
    while time.time()<until:time.sleep(min(30,until-time.time()))
  t=json.loads((H/'TALLY-resume.json').read_text());attempt=t['next_unused_id']
  r=subprocess.run(['python3',str(H/'compile_resume.py'),m])
  event(module=m,kind='submission_result',attempt=attempt,exit=r.returncode)
  if r.returncode==0:break
  if r.returncode!=78:raise SystemExit(r.returncode)
  refusals+=1
  if refusals>=10:
   event(module=m,kind='ten_refusals_compile_free_review',refusals=refusals)
   raise SystemExit(78)
