"""Sequential focused proof targets; existing admission wrapper enforces caps/cooldown."""
from pathlib import Path
import json,time,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
for m in sys.argv[1:]:
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
