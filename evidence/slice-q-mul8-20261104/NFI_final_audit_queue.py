from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(24,'lean','NFI_Driver'),(25,'linkaudit','NFI_Driver'),(26,'auditbin','fixtures'),(27,'auditbin','scan')]+[(28+i,'auditbin',f'proof{i}') for i in range(23)]
for i,kind,target in jobs:
 a=f'NFI_L{i:03}'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NFI_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 print(a,kind,target,'exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
