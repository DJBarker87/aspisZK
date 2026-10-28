"""Own serial transport queue; shared reservation and prover backends unchanged."""
from pathlib import Path
import json,subprocess,time,sys,hashlib
B=Path(__file__).resolve().parent
plan=json.loads((B/'NCD_focus2_plan.json').read_text());states=plan['states'];report=[]
assert all(r['module'].startswith('NCD_') for r in plan['rows'])
def save():
 (B/'NCD_focus2_state.json').write_text(json.dumps(dict(status='running',states=states,report=report),indent=2)+'\n')
for row in plan['rows']:
 a=row['cfg']['attempt'];m=row['module']
 if any(d.startswith('NCD_') and not states.get(d,False) for d in row['imports']):
  states[m]=False;report.append(dict(attempt=a,module=m,status='BLOCKED predecessor'));save();continue
 assert not (B/a/'receipt.json').exists(),'no duplicate attempt'
 for retry in range(11):
  dest=B/(a+'-reservation.json')
  with (B/(a+f'-barrier-{retry}.log')).open('w') as f:
   r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(dest)],stdout=f,stderr=subprocess.STDOUT)
  try:ad=json.loads(dest.read_text())
  except (FileNotFoundError,json.JSONDecodeError):
   if retry==0:time.sleep(30);continue
   raise SystemExit('STOP missing admission JSON')
  if r.returncode==0 and ad.get('allowed') is True:break
  if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
  raise SystemExit('STOP admission failure')
 else:raise SystemExit('STOP admission exhausted')
 cfg=row['cfg'];cfg['reservation_retries']=retry
 pins=json.loads((B/'NCD_LIBRARY_PIN.json').read_text())
 assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==h['sha256'] for p,h in pins.items()),'Aeneas pin drift'
 src=B/cfg['sources'][0];assert hashlib.sha256(src.read_bytes()).hexdigest()==row['source_sha256']
 (B/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 command=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','S2W_lean_host.py',a+'.json']
 with (B/(a+'-launcher.log')).open('wb') as log:r=subprocess.run(command,cwd=B,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT)
 p=B/a/'receipt.json'
 if not p.exists():
  report.append(dict(attempt=a,module=m,status='STOP no receipt',launcher_exit=r.returncode));save();raise SystemExit('STOP no receipt '+a)
 receipt=json.loads(p.read_text());states[m]=receipt['exit_status']==0
 report.append(dict(attempt=a,module=m,status='PASS' if states[m] else 'FAIL',exit_status=receipt['exit_status']))
 save()
(B/'NCD_focus2_state.json').write_text(json.dumps(dict(status='terminal',states=states,report=report),indent=2)+'\n')
