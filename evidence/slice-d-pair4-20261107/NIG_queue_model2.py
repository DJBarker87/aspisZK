from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L008','NIG_ShiftInspect'),('NIG_L009','NIG_NewDomain'),('NIG_L010','NIG_BothBranches')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 # A diagnostic may deliberately contain failed #checks. Preserve and continue.
 if r.returncode and t!='NIG_ShiftInspect':raise SystemExit('Review '+a)
