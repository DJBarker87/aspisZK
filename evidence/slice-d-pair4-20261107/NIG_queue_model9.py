from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L045','NIG_Geometry'),('NIG_L046','NIG_FinishConcrete')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
