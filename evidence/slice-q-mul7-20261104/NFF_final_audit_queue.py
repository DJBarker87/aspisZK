from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[(43,'lean','NFF_Driver'),(44,'linkaudit','NFF_Driver'),(45,'auditbin','scan'),(46,'auditbin','fixtures')]+[(47+i,'auditbin',f'proof{i}') for i in range(14)]
for i,kind,target in jobs:
 a=f'NFF_L{i:03}'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NFF_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 print(a,kind,target,'exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
