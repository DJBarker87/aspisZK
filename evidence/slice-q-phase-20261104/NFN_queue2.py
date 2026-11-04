from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i in range(4,9):
 a=f'NFN_L{i+7:03}';module=f'NFN_GeometryPart{i:02}'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NFN_run.py'),a,'lean',module],stdout=f,stderr=subprocess.STDOUT)
 print(a,module,'exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
