from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L047','NIG_FinishAlpha'),('NIG_L048','NIG_PairTail')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
