from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,n in [(12,'NFI_TailTrace'),(13,'NFI_PrivateCuts'),(14,'NFI_OuterActual'),(15,'NFI_OpeningFrame'),(16,'NFI_SingleTrace')]:
 a=f'NFI_L{i:03}'
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_run.py'),a,'lean',n],stdout=out,stderr=subprocess.STDOUT)
 print(a,n,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
