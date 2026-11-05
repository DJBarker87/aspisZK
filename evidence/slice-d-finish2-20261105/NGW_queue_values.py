from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,n in [('NGW_L023','NGW_RefLinear'),('NGW_L024','NGW_PointValue')]:
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'lean',n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
