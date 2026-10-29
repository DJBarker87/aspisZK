from pathlib import Path
import json,subprocess,time
D=Path('/home/dombarker/project-offloads/codex-pv-fix-20261028')
records={r['module']:r for r in json.loads((D/'preflight.json').read_text())['rdcd']['projects']};safe=set(json.loads((D/'resume-cache-check.json').read_text()));order=[]
def visit(m):
 if m not in records or m in safe or m in order:return
 for j in records[m]['imports']:visit(j['module'])
 order.append(m)
visit('R1Z/PV_RDCD_Op109Audit');order.append('R1Z/PV_FIX_V213Audit');visit('R1Z/PV_RDCD_FinalManifest')
(D/'resume-execution-order.json').write_text(json.dumps(order,indent=2)+'\n');print('ORDER',json.dumps(order),flush=True)
for a,m in enumerate(order[:40],62100):
 for retry in range(11):
  p=subprocess.run(['python3',str(D/'resume-run.py'),str(a),'rdcd',m])
  if p.returncode!=78:break
  if retry==10:raise SystemExit('admission retries exhausted')
  for _ in range(3):time.sleep(60)
 if p.returncode:raise SystemExit(p.returncode)
print('DONE',min(len(order),40),'attempts; remaining',len(order[40:]),flush=True)
