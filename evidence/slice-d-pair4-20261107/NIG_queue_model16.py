from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L068','NIG_PairShared'),('NIG_L069','NIG_PairCanonical')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
