"""LIBC-owned serial proof client; each child uses the unchanged capped launcher."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
start=int(sys.argv[1])
for n,target in enumerate(sys.argv[2:],start):
 a=f'LIBC_L{n:03d}'
 r=subprocess.run([sys.executable,str(E/'LIBC_run.py'),a,'lean',target])
 if r.returncode:sys.exit(r.returncode)
 subprocess.run(['git','add',str(E)],check=True)
 subprocess.run(['git','commit','-q','-m','Prove '+target+' library laws'],check=True)
 print(a+' committed '+target,flush=True)
