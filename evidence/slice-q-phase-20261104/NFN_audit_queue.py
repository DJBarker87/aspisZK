from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[(55,'auditbin','fixtures')]+[(57+i,'auditbin',f'proof{i}') for i in range(7)]
for i,kind,target in jobs:
 a=f'NFN_L{i:03}'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NFN_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 print(a,kind,target,'exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
