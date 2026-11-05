from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L038','NIG_Geometry'),('NIG_L039','NIG_PairFrames'),('NIG_L040','NIG_Slots')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
