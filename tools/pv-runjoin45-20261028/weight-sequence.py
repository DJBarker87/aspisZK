"""Sequential pinned weight prerequisites, one module and one scope per attempt."""
from pathlib import Path
import json,subprocess,time,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin45-20261028';T=R/'tools/pv-runjoin45-20261028'
order=json.loads((E/'weight-source-staging.json').read_text())['order']
start=int(sys.argv[1]);limit=int(sys.argv[2]);accepted={v['module'] for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
a=start
for m in order:
 if m in accepted:continue
 if a>=limit:break
 for retry in range(11):
  prior=[json.loads(p.read_text()) for p in E.glob('refusal-*.json')]
  deadline=max((x['epoch']+180 for x in prior),default=0)
  while time.time()<deadline:
   print('COOLDOWN; no compiler launched; remaining',round(deadline-time.time(),1),flush=True);time.sleep(min(45,deadline-time.time()))
  r=subprocess.run([sys.executable,str(T/'compile.py'),str(a),'0',m],cwd=R)
  if r.returncode==0:break
  if r.returncode not in (77,78):raise SystemExit(r.returncode)
  if retry==10:raise SystemExit(78)
 accepted.add(m);a+=1
print('WEIGHT SEQUENCE END; next ID',a,'accepted prerequisite modules',sum(m in accepted for m in order),flush=True)
