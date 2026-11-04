from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[(22,'lean','NFM_Driver'),(23,'linkaudit','NFM_Driver'),(24,'auditbin','fixtures'),(25,'lean','NFM_Scanner'),(26,'linkaudit','NFM_Scanner'),(27,'auditbin','scan')]
for i,kind,target in jobs:
 a=f'NFM_L{i:03}'
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFM_run.py'),a,kind,target],stdout=out,stderr=subprocess.STDOUT)
 print(a,target,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
