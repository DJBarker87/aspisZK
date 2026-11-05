from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L071','NIG_PairCanonical'),('NIG_L072','NIG_PairExport')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
