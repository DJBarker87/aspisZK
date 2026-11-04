"""One module per admitted capped attempt; never rebuild a package."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent;n=int(sys.argv[1])
for name in sys.argv[2:]:
 assert n<=60
 r=subprocess.run([sys.executable,str(E/'NEX_run.py'),f'NEX_L{n:03}',name],capture_output=True,text=True)
 print(name,r.stdout,r.stderr,flush=True);n+=1
 if r.returncode:raise SystemExit(r.returncode)
