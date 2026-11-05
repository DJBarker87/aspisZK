from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L041','NIG_Geometry'),('NIG_L042','NIG_PairFrames')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
