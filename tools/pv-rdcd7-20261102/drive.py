"""Serial focused Lean plan; cooldowns/refusals retained by the existing wrapper."""
from pathlib import Path
import subprocess,json,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102'
plan=json.load(open(E/'source-resolution.json'));n=int(sys.argv[1]);through=sys.argv[2]
passed={json.loads(p.read_text()).get('module') for p in E.glob('lean-*/receipt.json') if json.loads(p.read_text())['exit']==0}
for dotted in plan['compile_order']:
 m=dotted.replace('.','/')
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
