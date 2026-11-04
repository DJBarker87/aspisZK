from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,n in [(16,'NFI_OpeningFrame'),(17,'NFI_SingleTrace'),(18,'NFI_WrapperTrace'),(19,'NFI_WrapperDomains')]:
 a=f'NFI_L{i:03}'
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_run.py'),a,'lean',n],stdout=out,stderr=subprocess.STDOUT)
 print(a,n,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
