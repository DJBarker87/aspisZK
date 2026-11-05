from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L010','NIG_NewDomain'),('NIG_L011','NIG_BothBranches'),('NIG_L012','NIG_Indices')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:raise SystemExit('Review '+a)
