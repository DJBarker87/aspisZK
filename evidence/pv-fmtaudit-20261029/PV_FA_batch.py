from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029')
jobs=[['lean','73704','authority','PV_FA_probe.lean'],['lean','73705','b3q','PV_FA_list.lean'],['lean','73706','ndr','PV_FA_list.lean'],['lean','73707','b3q','PV_FA_raw.lean'],['lean','73708','ndr','PV_FA_raw.lean'],['source','73709']]
for j in jobs:
 r=subprocess.run([sys.executable,str(H/'PV_FA_launch.py'),*j],cwd=H)
 if r.returncode:sys.exit(r.returncode)
