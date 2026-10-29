from pathlib import Path
import subprocess,json,time
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029')
commands=[(['native_d188.py','negative'],1)]+[(['native_extra.py',mode],101 if mode.endswith('negative')else 0)for mode in ['bit-positive','bit-negative','iterator-positive','iterator-negative','format-positive','format-negative']]
for command,expected in commands:
 for retry in range(11):
  p=H/'admission-not-before.json'
  while p.exists() and (remaining:=json.loads(p.read_text())['epoch']-time.time())>0:time.sleep(min(30,remaining))
  r=subprocess.run(['python3',*command],cwd=H)
  if r.returncode!=78:break
 assert r.returncode==expected,(command,r.returncode,expected)
(H/'native-tail-complete.json').write_text(json.dumps(dict(status='pass',commands=commands))+'\n')
