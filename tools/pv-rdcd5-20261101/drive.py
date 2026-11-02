"""Serial focused dependency compilation; stop immediately on proof failure."""
from pathlib import Path
import json,subprocess,sys,time,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd5-20261101'
through=sys.argv[1];plan=json.load(open(E/'source-resolution.json'))
pre=json.load(open(E/'preflight-result.json'));passed=set(pre['reused'])
used=[]
for p in E.glob('lean-*/receipt.json'):
 j=json.load(open(p));used.append(j['attempt'])
 if j['exit']==0 and hashlib.sha256((R/j['source_path']).read_bytes()).hexdigest()==j['source_sha256']:passed.add(j['module'])
n=max(used+[78199])+1
for m in plan['compile_order']:
 key=m.replace('.','/')
 if key not in passed:
  assert n<78297,'audit reserve'
  while True:
   if (E/'last-launch.json').exists():
    remaining=182-(time.time()-json.load(open(E/'last-launch.json'))['epoch'])
    while remaining>0:
     print('Cooldown',round(remaining),'seconds; next',n,key,flush=True);time.sleep(min(45,remaining));remaining=182-(time.time()-json.load(open(E/'last-launch.json'))['epoch'])
   print('Compiling',n,key,flush=True)
   r=subprocess.run([sys.executable,str(R/'tools/pv-rdcd5-20261101/lean.py'),str(n),key],cwd=R)
   if r.returncode in [78,79]:
    print('Uncharged admission refusal',r.returncode,flush=True)
    for _ in range(4):time.sleep(45);print('Admission cooldown',flush=True)
    continue
   if r.returncode:sys.exit(r.returncode)
   break
  n+=1
 if m==through:break
