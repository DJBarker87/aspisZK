from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L064','NIG_PairS2Body'),('NIG_L065','NIG_PairShared')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
