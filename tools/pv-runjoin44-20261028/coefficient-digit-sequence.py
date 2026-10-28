"""Sequential focused prerequisite launches; retain IDs on admission refusals."""
from pathlib import Path
import json,subprocess,time,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin44-20261028'
for item in json.loads((E/'coefficient-digit-order.json').read_text()):
 a=item['attempt'];m=item['module'];receipt=E/f'receipt-{a}.json'
 subprocess.run(['python3',str(R/'tools/pv-runjoin44-20261028/stage-target.py'),m],check=True,cwd=R)
 if receipt.exists():
  x=json.loads(receipt.read_text());assert x['accepted'] and x['modules']==[m],'failed source is never rerun unchanged'
  continue
 for retry in range(11):
  refusals=[json.loads(p.read_text()) for p in E.glob('refusal-*.json')]
  deadline=max((r['epoch']+180 for r in refusals),default=0)
  while time.time()<deadline:
   duration=min(45,deadline-time.time());print('COOLDOWN',a,round(deadline-time.time(),1),'s; no compiler started',flush=True);time.sleep(duration)
  r=subprocess.run(['python3',str(R/'tools/pv-runjoin44-20261028/compile.py'),str(a),'0',m],cwd=R)
  if r.returncode==0:break
  if r.returncode not in [77,78]:raise SystemExit(r.returncode)
  if retry==10:print('ten admission retries; return to compile-free work',flush=True);raise SystemExit(78)
 else:raise AssertionError('unreachable')
print('ALL 4 REMAINING DIGITS ACCEPTED',flush=True)
