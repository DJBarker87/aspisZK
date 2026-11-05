from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L073','NIG_PairExport'),('NIG_L074','NIG_PairCaller'),('NIG_L075','NIG_FinishPacket')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
