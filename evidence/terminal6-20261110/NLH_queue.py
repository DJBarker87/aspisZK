"""Sequential own input queue: stop on first failed focused target."""
from pathlib import Path
import subprocess,sys,json
p=Path(__file__).resolve().parent
start=int(sys.argv[1])
for i,module in enumerate(sys.argv[2:],start):
 a=f'NLH_L{i:03}'
 subprocess.run([sys.executable,str(p/'NLH_make.py'),a,module],check=True)
 r=subprocess.run([sys.executable,str(p/'NLH_run.py'),a])
 print(json.dumps(dict(attempt=a,module=module,exit=r.returncode)),flush=True)
 if r.returncode:sys.exit(r.returncode)
