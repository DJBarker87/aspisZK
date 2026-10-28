"""Focused dependency restoration; never replay a present accepted object."""
from pathlib import Path
import json,hashlib,time,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027');plan=json.loads((H/'resume-dependency-plan.json').read_text())['topological_order']
for m in plan:
 p=H/'lean'/(m+'.lean');o=H/'lean-objects'/(m+'.olean');t=json.loads((H/'TALLY-resume.json').read_text());sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if o.exists() and any(r['module']==m and r['exit']==0 and json.loads(Path(r['receipt']).read_text())['source_sha256']==sha for r in t['receipts']):
  print(json.dumps({'module':m,'reused_present_accepted_object':True}),flush=True);continue
 if t['lean_attempts']>=97:raise SystemExit('97 focused attempts reached; three audit attempts retained')
 refusals=0
 while True:
  if (H/'admission-not-before.json').exists():
   until=json.loads((H/'admission-not-before.json').read_text())['epoch']
   if time.time()<until:print(json.dumps({'module':m,'cooldown_not_before':until}),flush=True)
   while time.time()<until:time.sleep(min(30,until-time.time()))
  r=subprocess.run(['python3',str(H/'compile_resume.py'),m])
  if r.returncode==0:break
  if r.returncode!=78:raise SystemExit(r.returncode)
  refusals+=1
  if refusals==10:raise SystemExit(78)
