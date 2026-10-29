from pathlib import Path
import subprocess,time,sys
D=Path('/home/dombarker/project-offloads/codex-pv-diag-20261029')
jobs=[('native15',['scan','12','13'])]+[(f'native{i+2:02}', ['scan',str(i)]) for i in range(14,46)]+[('native48',['backtrace']),('native49',['machine']),('native50',['aggregate'])]
for label,args in jobs:
 for refusal in range(11):
  p=subprocess.run(['python3',str(D/'run.py'),label,*args])
  if p.returncode!=78:break
  if refusal==10:sys.exit(78)
  # Three bounded waits; the caller remains able to inspect progress.
  for _ in range(3):time.sleep(60)
 if p.returncode:sys.exit(p.returncode)
