"""Serial, fail-fast dependency replay; every launch retains normal admission."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
start,stop,attempt=map(int,sys.argv[1:])
for i in range(start,stop):
 a=f'NFY_L{attempt:03}';m=f'NFY_Part{i:03}'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NFY_run.py'),a,'lean',m],stdout=f,stderr=subprocess.STDOUT)
 print(a,m,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
 attempt+=1
