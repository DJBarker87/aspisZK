from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=json.loads((E/'NIL_SUPPORT_PLAN.json').read_text())
for a,k,m in jobs:
 p=E/a/'receipt.json'
 if not p.exists():
  r=subprocess.run([sys.executable,str(E/'NIL_run.py'),a,k,m],capture_output=True,text=True)
  (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 if not p.exists():raise RuntimeError('prelaunch '+a)
 x=json.loads(p.read_text());print(a,k,m,x['exit_status'],flush=True)
 if x['exit_status']:raise RuntimeError('isolate '+a)
