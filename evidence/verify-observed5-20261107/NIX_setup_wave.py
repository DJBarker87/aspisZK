from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
for a in ['NIX_L042','NIX_L043','NIX_L044']:
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NIX_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:break
