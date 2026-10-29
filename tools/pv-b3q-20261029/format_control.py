from pathlib import Path
import subprocess,json,time
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029')
for mode,expected in [('format-placeholder-positive',0),('format-placeholder-negative',101)]:
 for retry in range(11):
  p=H/'admission-not-before.json'
  while p.exists()and(d:=json.loads(p.read_text())['epoch']-time.time())>0:time.sleep(min(30,d))
  r=subprocess.run(['python3','native_extra.py',mode],cwd=H)
  if r.returncode!=78:break
 assert r.returncode==expected,(mode,r.returncode)
