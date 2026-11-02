"""Serial focused Lean plan; cooldowns/refusals retained by the existing wrapper."""
from pathlib import Path
import subprocess,json,sys,time,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102'
plan=json.load(open(E/'source-resolution.json'));n=int(sys.argv[1]);through=sys.argv[2]
passed=set()
for p in E.glob('lean-*/receipt.json'):
 j=json.loads(p.read_text())
 if j['exit']==0 and j.get('source_path') and hashlib.sha256((R/j['source_path']).read_bytes()).hexdigest()==j['source_sha256']:
  passed.add(j['module'])
# Rebuild every consumer when a previously accepted owned dependency changed.
known={json.loads(p.read_text()).get('module') for p in E.glob('lean-*/receipt.json') if json.loads(p.read_text())['exit']==0}
invalid=known-passed
for dotted in plan['compile_order']:
 m=dotted.replace('.','/')
 if any(dep.replace('.','/') in invalid for dep in plan['modules'][dotted]['imports']):
  passed.discard(m);invalid.add(m)

for dotted in plan['compile_order']:
 m=dotted.replace('.','/')
 if plan.get('module_kinds',{}).get(dotted,'ordinary-focused')!='ordinary-focused':continue
 if m in passed:continue
 assert n<90797
 for tries in range(11):
  while (E/'last-launch.json').exists() and time.time()-json.load(open(E/'last-launch.json'))['epoch']<183:
   time.sleep(min(30,183-(time.time()-json.load(open(E/'last-launch.json'))['epoch'])))
  print('Launching',n,m,flush=True)
  r=subprocess.run([sys.executable,str(R/'tools/pv-rdcd7-20261102/lean.py'),str(n),m],cwd=R)
  if r.returncode in [78,79]:
   print('Uncharged refusal; waiting full cooldown before same ID',flush=True)
   # scope.py may refuse before any launch clock is written.
   for _ in range(6):time.sleep(30)
   continue
  if r.returncode:sys.exit(r.returncode)
  break
 else:raise RuntimeError('Repeated admission refusals')
 n+=1
 if dotted==through:break
