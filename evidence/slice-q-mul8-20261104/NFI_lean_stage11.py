from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,n in [(21,'NFI_FailurePrefixes'),(22,'NFI_SingleDomains'),(23,'NFI_CombinedFinal')]:
 a=f'NFI_L{i:03}'
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_run.py'),a,'lean',n],stdout=out,stderr=subprocess.STDOUT)
 print(a,n,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
