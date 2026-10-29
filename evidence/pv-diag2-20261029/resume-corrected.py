from pathlib import Path
import subprocess,sys
D=Path(__file__).parent
for name,args in [('log-guard.py',[]),('body-bindings.py',['log']),('retry-binding.py',[])]:
 r=subprocess.run([sys.executable,str(D/name),*args]);
 if r.returncode:raise SystemExit(r.returncode)
