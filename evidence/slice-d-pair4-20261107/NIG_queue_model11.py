from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L049','NIG_PairTail'),('NIG_L050','NIG_FinishExport')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
