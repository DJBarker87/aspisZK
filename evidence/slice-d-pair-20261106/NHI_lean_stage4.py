from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,m in enumerate(['GroupTables','PartialIndexExtracted','PartialIndex','HighDotLoop','PartialDotLoop','GroupAlgebra'],53):
 a=f'NHI_L{n:03d}'
 with(E/(a+'-queue.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NHI_run.py'),a,'lean','NHI_'+m],stdout=f,stderr=subprocess.STDOUT)
 print(a,m,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
