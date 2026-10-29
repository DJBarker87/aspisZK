"""Run focused modules sequentially and preserve complete cooldowns."""
from pathlib import Path
import subprocess,time,json,sys
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029')
for arg in sys.argv[1:]:
 a,m=arg.split(':',1)
 for retry in range(11):
  p=H/'admission-not-before.json'
  while p.exists()and (d:=json.loads(p.read_text())['epoch']-time.time())>0:time.sleep(min(30,d))
  r=subprocess.run(['python3',str(H/'compile.py'),m,a],cwd=H)
  if r.returncode!=78:break
 if r.returncode:raise SystemExit(r.returncode)
