"""Sequential focused proof targets; existing admission wrapper enforces caps/cooldown."""
from pathlib import Path
import json,time,subprocess,sys,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
targets=sys.argv[1:]
if targets and targets[0]=='--plan':targets=json.loads((H/targets[1]).read_text())['topological_order']
for m in targets:
 t=json.loads((H/'TALLY-d324.json').read_text())
 src=H/'lean'/(m.replace('.','/')+'.lean');obj=H/'lean-objects'/(m.replace('.','/')+'.olean')
 sha=hashlib.sha256(src.read_bytes()).hexdigest()
 if obj.is_file() and any(r['module']==m and r['exit']==0 and json.loads(Path(r['receipt']).read_text())['source_sha256']==sha for r in t['receipts']):
  print(json.dumps({'module':m,'reused_own_accepted_object':True}),flush=True);continue
 if t['lean_attempts']>=97:raise SystemExit('focused budget exhausted; audit IDs retained')
 refusals=0
 while True:
  c=H/'admission-not-before.json'
  if c.exists():
   until=json.loads(c.read_text())['epoch']
   while time.time()<until:time.sleep(min(30,until-time.time()))
  r=subprocess.run(['python3',str(H/'compile_d324.py'),m])
  if r.returncode==0:break
  if r.returncode!=78:raise SystemExit(r.returncode)
  refusals+=1
  if refusals>=10:raise SystemExit(78)
