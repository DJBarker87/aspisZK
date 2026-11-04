from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,n in [(10,'NFI_TailTrace'),(11,'NFI_PrivateCuts'),(12,'NFI_OuterActual'),(13,'NFI_OpeningFrame')]:
 a=f'NFI_L{i:03}'
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_run.py'),a,'lean',n],stdout=out,stderr=subprocess.STDOUT)
 print(a,n,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
