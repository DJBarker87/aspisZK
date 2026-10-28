"""Sequential focused proof queue; full admission cooldowns and no failed reruns."""
import subprocess,sys,time,json,pathlib
E=pathlib.Path('evidence/pv-rjdec-20261028')
a=int(sys.argv[1])
for m in sys.argv[2:]:
 for retry in range(11):
  refusals=list(E.glob('refusal-*.json'))
  deadline=max([json.loads(p.read_text())['epoch']+180 for p in refusals] or [0])
  while time.time()<deadline:
   left=deadline-time.time();print('COOLDOWN',a,round(left),flush=True);time.sleep(min(60,left))
  r=subprocess.run(['python3','tools/pv-rjdec-20261028/compile.py',str(a),'0',m])
  if r.returncode not in (77,78):break
  if retry==10:sys.exit(r.returncode)
 if r.returncode:sys.exit(r.returncode)
 a+=1
