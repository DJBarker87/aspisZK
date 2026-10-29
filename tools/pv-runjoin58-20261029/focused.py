"""Stage and compile one changed module; retry only unlaunched admissions."""
from pathlib import Path
import subprocess,sys,time,json
R=Path(__file__).resolve().parents[2];T=Path(__file__).parent;E=R/'evidence/pv-runjoin58-20261029'
a,m=sys.argv[1:]
subprocess.run([sys.executable,str(T/'stage-target.py'),m],check=True)
for retry in range(11):
 prior=[json.loads(p.read_text()) for p in E.glob('refusal-*.json')]
 deadline=max((p['epoch']+180 for p in prior),default=0)
 while time.time()<deadline:
  print('Cooldown remaining',round(deadline-time.time()),flush=True);time.sleep(min(30,deadline-time.time()))
 r=subprocess.run([sys.executable,str(T/'compile.py'),a,'0',m])
 if r.returncode not in (77,78):sys.exit(r.returncode)
raise SystemExit(78)
