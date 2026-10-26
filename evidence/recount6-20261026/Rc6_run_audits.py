"""Run planned focused inventories sequentially; stop on any unsuccessful scope."""
from pathlib import Path
import subprocess,sys,json
P=Path(__file__).resolve().parent
start=int(sys.argv[1]);end=int(sys.argv[2])
plan=json.loads((P/'Rc6_audit_plan.json').read_text())
for a in plan:
 n=int(a['attempt'].split('_')[1])
 if not start<=n<=end:continue
 print(a['attempt'],a['module'],flush=True)
 r=subprocess.run([sys.executable,str(P/'Rc6_compile.py'),str(n),a['module']],capture_output=True,text=True)
 (P/(a['attempt']+'-launch.log')).write_text(r.stdout+r.stderr)
 print('exit',r.returncode,flush=True)
 if r.returncode:
  print(r.stdout+r.stderr,flush=True);sys.exit(r.returncode)
