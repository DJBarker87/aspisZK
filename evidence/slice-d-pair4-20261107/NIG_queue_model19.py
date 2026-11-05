from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [('NIG_L076','NIG_PairExport'),('NIG_L077','NIG_FinishPacket')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
