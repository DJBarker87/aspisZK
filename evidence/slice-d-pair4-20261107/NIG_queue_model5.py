from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for a,t in [('NIG_L020','NIG_FilledCoverage'),('NIG_L021','NIG_LibraDomain'),('NIG_L022','NIG_Indices')]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'lean',t])
 if r.returncode:print('REVIEW',a,flush=True)
