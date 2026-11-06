from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,t in [('NKY_L070','NKY_BoxPost'),('NKY_L071','NKY_BoxPostWindows'),('NKY_L072','NKY_BoxSource')]:
 r=subprocess.run([sys.executable,str(E/'NKY_run.py'),a,'lean',t])
 if r.returncode:raise SystemExit(r.returncode)
 print(a,t,'complete',flush=True)
