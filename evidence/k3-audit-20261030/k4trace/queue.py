"""Sequential driver; no retry after a checked positive failure or timeout."""
from pathlib import Path
import subprocess,json,time,sys
E=Path(__file__).resolve().parent;H='/home/dombarker/project-offloads/codex-pv-k4trace-20261104'
ids=[r for r in json.loads((E/'runs.json').read_text()) if r['id']!='K93512' and (len(sys.argv)==1 or r['id'] in sys.argv[1:])]
for row in ids:
 ident=row['id'];refusals=0
 while True:
  r=subprocess.run(['ssh','dombarker@100.108.41.90','python3',H+'/host_run.py',ident],text=True,capture_output=True)
  print(ident,r.returncode,r.stdout.strip(),r.stderr.strip(),flush=True)
  if r.returncode==79:
   remaining=json.loads(r.stdout)['cooldown_seconds']
   while remaining>0:
    t=min(remaining+.1,60);time.sleep(t);remaining-=t
   continue
  if r.returncode==78:
   refusals+=1
   if refusals>10:sys.exit('ten reservation refusals')
   for _ in range(3):time.sleep(60)
   continue
  if r.returncode==255:sys.exit('transport unresolved; recover without resubmission')
  break
 subprocess.run([sys.executable,str(E/'collect.py'),ident],check=True)
 subprocess.run([sys.executable,str(E/'inspect_trace.py'),ident],check=True)
 s=(E/'host'/ident/'output.log').read_text()
 if row['negative'] is False and (r.returncode!=0 or 'VERIFICATION:- FAILED' in s):sys.exit('POSITIVE FAILURE: classify before any further work')
 if row['negative']=='included':
  # Three selected harnesses only; all controls may fail, the positive must pass.
  if 'Complete - 1 successfully verified harnesses, 2 failures, 3 total.' not in s:sys.exit('projection verdict unexpected: classify before any further work')
 if r.returncode not in (0,1):sys.exit('setup/timeout/resource error: no unchanged retry')
 print('RETAINED',ident,flush=True)
