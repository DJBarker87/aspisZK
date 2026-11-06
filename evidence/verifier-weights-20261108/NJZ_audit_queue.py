from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
jobs=[(33,'lean','NJZ_COMBINED_IMPORT'),(34,'lean','NJZ_ProofDriver'),(35,'link','NJZ_ProofDriver'),(36,'audit','fixtures'),(37,'audit','all'),(38,'lean','NJZ_Driver'),(39,'link','NJZ_Driver'),(40,'audit','scan')]
for n,kind,target in jobs:
 a=f'NJZ_L{n:03d}'
 with (E/(a+'-summary.log')).open('w') as out:r=subprocess.run([sys.executable,str(E/'NJZ_run.py'),a,kind,target],stdout=out,stderr=subprocess.STDOUT)
 print(a,kind,target,'exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
