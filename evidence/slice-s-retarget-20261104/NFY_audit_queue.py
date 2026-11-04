"""Serial final audit stages; scopes remain individually admitted and metered."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(101,'lean','NFY_ProofDriver'),(102,'lean','NFY_Driver'),(103,'link','NFY_ProofDriver'),(104,'link','NFY_Driver'),(105,'audit','fixtures'),(106,'audit','scan')]
jobs += [(107+i,'audit','batch'+str(i)) for i in range(4)]
for n,kind,target in jobs:
 a=f'NFY_L{n:03}'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NFY_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 print(a,kind,target,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
