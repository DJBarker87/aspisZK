"""Own serial validation controller. Shared admission and runners are unchanged."""
from pathlib import Path
import subprocess,json,sys,time,hashlib
B=Path(__file__).resolve().parent
spec=json.loads((B/sys.argv[1]).read_text());items=[dict(spec['base'],**target) for target in spec['targets']]
for cfg in items:
 a=cfg['attempt'];assert not (B/a/'receipt.json').exists(),('already submitted',a)
 for n in range(11):
  p=B/(a+'-barrier-'+str(n)+'.log');q=B/(a+'-reservation.json')
  with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
  ad=json.loads(q.read_text()) if q.exists() else None
  print(json.dumps(dict(event='admission',attempt=a,trial=n,exit=r.returncode,reservation=ad,log=p.read_text())),flush=True)
  if ad is None:
   if n==0:time.sleep(30);continue
   raise SystemExit('STOP missing reservation')
  if r.returncode==0 and ad.get('allowed') is True:break
  if (r.returncode==78 or ad.get('allowed') is False) and n<10:time.sleep(180);continue
  raise SystemExit('STOP admission failure')
 else:raise SystemExit('STOP admission exhausted')
 (B/(a+'.json')).write_text(json.dumps(cfg,indent=2))
 cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','S2W_run_host.py',a+'.json']
 print(json.dumps(dict(event='submitted',attempt=a,command=cmd)),flush=True)
 r=subprocess.run(cmd,cwd=B,capture_output=True,text=True)
 assert (B/a/'receipt.json').is_file(),('STOP submitted without receipt',a,r.stdout,r.stderr)
 names=[a+'.json',a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph.json',a+'-metadata.stderr']
 result={n:(B/n).read_text() for n in names if (B/n).is_file()}
 print(json.dumps(dict(event='result',attempt=a,files=result,launcher=r.stdout+r.stderr)),flush=True)
 rc=json.loads(result[a+'/receipt.json'])
 if rc['exit_status'] not in [0,1]:raise SystemExit('STOP exceptional exit; inspect and split')
 if not json.loads(result[a+'-graph.json']).get('lock_unchanged'):raise SystemExit('STOP lock mismatch')
