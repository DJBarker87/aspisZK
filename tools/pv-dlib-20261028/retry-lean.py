"""Bounded sequential admission retries; compiler failure is returned, never retried."""
from pathlib import Path
import subprocess,sys,time,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028'
modules=sys.argv[1:];assert modules
for _ in range(10):
 while True:
  c=json.loads((E/'COOLDOWN.json').read_text());remain=c.get('ready_epoch',0)-time.time()
  if remain<=0:break
  print('cooldown; no host request; remaining',round(remain),flush=True);time.sleep(min(60,remain+0.2))
 t=json.loads((E/'TALLY.json').read_text());n=max(t['used_ids'])+1
 assert n<43497, 'focused IDs exhausted; audits reserved'
 print('submit',n,modules,flush=True)
 with (E/f'{n}-driver.log').open('w') as out:
  cmd=([sys.executable,str(R/'tools/pv-dlib-20261028/lean.py'),str(n),modules[0]] if len(modules)==1 else [sys.executable,str(R/'tools/pv-dlib-20261028/batch-lean.py'),*modules])
  r=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT)
 print('result',n,r.returncode,flush=True)
 if r.returncode!=78:sys.exit(r.returncode)
print('ten refusals; compile-free review required',flush=True)
sys.exit(78)
