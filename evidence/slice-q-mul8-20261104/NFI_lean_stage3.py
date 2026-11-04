from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,n in [(7,'NFI_TraceResult'),(8,'NFI_TailTrace'),(9,'NFI_PrivateCuts'),(10,'NFI_OuterActual'),(11,'NFI_OpeningFrame')]:
 a=f'NFI_L{i:03}'
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_run.py'),a,'lean',n],stdout=out,stderr=subprocess.STDOUT)
 print(a,n,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
