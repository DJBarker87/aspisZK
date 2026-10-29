from pathlib import Path
import subprocess,json,time
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029')
for i,m in enumerate(['FmtInspect','ArrayView','ArrayBorrow','BitCounts','Range','Iterator4','IteratorAlignment'],70237):
 r=subprocess.run(['python3',str(H/'serial.py'),str(i)+':PV_B3Q_'+m],cwd=H)
 if r.returncode:raise SystemExit(r.returncode)
