from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(49+i,'audit','window'+str(42+i))for i in range(9)]+[(58,'lean','NNK_FinalStatements'),(59,'audit','scan'),(60,'audit','all-close')]
for n,kind,mode in jobs:
 a=f'NNK_L{n:03}';assert not(E/a).exists()
 with(E/(a+'-client.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NNK_run.py'),a,kind,mode],stdout=f,stderr=subprocess.STDOUT)
 print(a,mode,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
