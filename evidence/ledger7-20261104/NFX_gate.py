"""Serial finite final audit plan; stop at the first failed child."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(24,'link','NFX_ProofDriver'),(25,'link','NFX_Driver'),(26,'audit','fixtures')]
n=len(json.loads((E/'NFX_AUDIT_ROOTS.json').read_text())['groups'])
jobs += [(27+i,'audit','batch'+str(i)) for i in range((n+9)//10)]
jobs += [(27+(n+9)//10,'audit','scan')]
for number,kind,target in jobs:
 a=f'NFX_L{number:03}';assert number<=40
 with (E/(a+'.client.log')).open('w') as out:r=subprocess.run([sys.executable,str(E/'NFX_run.py'),a,kind,target],stdout=out,stderr=subprocess.STDOUT)
 print(a,kind,target,'client exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
