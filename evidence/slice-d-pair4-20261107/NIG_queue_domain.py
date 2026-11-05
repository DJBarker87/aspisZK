from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L006','NIG_Indices'),('NIG_L007','NIG_BoxModel'),('NIG_L008','NIG_FInM31')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:raise SystemExit('Review '+a)
