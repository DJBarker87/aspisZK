"""Own serial dependency recovery. No shared launcher edits, cap increases,
timeout retries, or alternate cached-source selection. Missing imports only."""
from pathlib import Path
import subprocess,sys,json,re
E=Path(__file__).resolve().parent

def missing(log):
 m=re.search(r"unknown module prefix '([^']+)'",log)
 return m.group(1) if m else None

def dep(m,stack=()):
 assert m not in stack,('dependency cycle',stack,m)
 before=set(E.glob('NBS_L*/receipt.json'))
 r=subprocess.run([sys.executable,str(E/'NBS_deps.py'),m],capture_output=True,text=True)
 print(r.stdout+r.stderr,flush=True)
 if r.returncode==0:return
 added=set(E.glob('NBS_L*/receipt.json'))-before
 assert added,('source selection/transport failure',m)
 failed=sorted(added)[-1];x=json.loads(failed.read_text())
 assert x['exit_status'] not in [124,137],('never rerun timed out/killed',m)
 log=(failed.parent/'stdout.log').read_text();need=missing(log)
 assert need,('not a missing import',failed)
 dep(need,(*stack,m));dep(m,stack)

p,module=sys.argv[1:]
# Recover an already observed missing dependency before issuing another
# identical pre-elaboration target attempt.
prior=[]
for receipt in E.glob('NBS_L*/receipt.json'):
 x=json.loads(receipt.read_text())
 if x.get('module')==module and x.get('exit_status')!=0:prior.append((x['attempt'],receipt))
if prior:
 last=max(prior)[1];need=missing((last.parent/'stdout.log').read_text())
 if need:dep(need)
for _ in range(30):
 n=1+len(list(E.glob('NBS_L[0-9][0-9][0-9].json')));assert n<=100
 a=f'NBS_L{n:03}'
 r=subprocess.run([sys.executable,str(E/'NBS_build.py'),a,p,module],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 receipt=E/a/'receipt.json';assert receipt.is_file(),r.stdout+r.stderr
 x=json.loads(receipt.read_text());print(a,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status']==0:
  print(r.stdout,flush=True);break
 assert x['exit_status'] not in [124,137],('no timeout/memory rerun',a)
 need=missing((E/a/'stdout.log').read_text())
 assert need,r.stdout+r.stderr
 dep(need)
else:raise RuntimeError('missing dependency limit')
