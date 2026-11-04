from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,module in [(11,'NFM_Cuts'),(12,'NFM_Single'),(13,'NFM_Domains'),(14,'NFM_Span')]:
 a=f'NFM_L{i:03}'
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFM_run.py'),a,'lean',module],stdout=out,stderr=subprocess.STDOUT)
 print(a,module,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
