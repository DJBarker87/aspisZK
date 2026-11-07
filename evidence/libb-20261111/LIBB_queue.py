"""Serial own-module compilation; commit each passing source stage."""
from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);mods=sys.argv[2:]
for n,m in enumerate(mods,start):
 a=f'LIBB_L{n:03d}'
 r=subprocess.run([sys.executable,str(E/'LIBB_run.py'),a,'lean',m])
 if r.returncode:sys.exit(r.returncode)
 assert not any(p.stat().st_size>20_000_000 for p in E.rglob('*') if p.is_file()),'oversize evidence'
 subprocess.run(['git','add','evidence/libb-20261111'],check=True)
 subprocess.run(['git','commit','-m','Validate '+m+' library stage'],check=True,stdout=subprocess.DEVNULL)
 print('committed '+m,flush=True)
