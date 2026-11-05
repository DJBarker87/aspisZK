from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L059','NIG_PairValues'),('NIG_L060','NIG_PairS2Body')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
