"""Sequential focused continuation checks; halt for any rejected/refused target."""
from pathlib import Path
import subprocess,sys,json
R=Path(__file__).resolve().parents[2]
start,first,last=map(int,sys.argv[1:])
for offset,i in enumerate(range(first,last+1)):
 a=start+offset;m=f'R1Z/PV_RE_Continue{i:03}'
 r=subprocess.run([sys.executable,str(R/'tools/pv-reach-20261027/resume-check.py'),str(a),m],cwd=R)
 if r.returncode:print('QUEUE HALTED',a,m,r.returncode,flush=True);sys.exit(r.returncode)
