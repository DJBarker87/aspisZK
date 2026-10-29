"""Wait for the charged predecessor, then run only sequential focused work."""
from pathlib import Path
import subprocess,json,time,sys
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029')
modules=[(70234,'FourSlice')]+list(enumerate(['MatrixFixture','IndexInspect']+['D188Fixture'+str(i)for i in range(10,15)],70225))
for i,m in modules:
 r=subprocess.run(['python3',str(H/'serial.py'),str(i)+':PV_B3Q_'+m],cwd=H)
 if r.returncode:raise SystemExit(r.returncode)
# No native scope is submitted concurrently with a Lean scope.
for cmd in [['native_d188.py'],['native_extra.py','matrix-linear'],['native_extra.py','byte-positive'],['native_extra.py','byte-negative']]:
 for retry in range(11):
  p=H/'admission-not-before.json'
  while p.exists()and(d:=json.loads(p.read_text())['epoch']-time.time())>0:time.sleep(min(30,d))
  r=subprocess.run(['python3',*cmd],cwd=H)
  if r.returncode!=78:break
 if cmd[-1]=='byte-negative':assert r.returncode!=0 and r.returncode!=78,'negative control did not fail'
 elif r.returncode:raise SystemExit(r.returncode)
(H/'continuation-done.json').write_text(json.dumps(dict(status='all requested focused compiles and four native scopes completed'))+'\n')
