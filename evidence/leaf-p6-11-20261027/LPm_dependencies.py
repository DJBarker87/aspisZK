"""Inventory absent private prerequisites and build unchanged source modules serially."""
from pathlib import Path
import subprocess,json,sys,shlex
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-leaf-p6-11-20261027'
C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
roots=[Path('lean'),Path('docs/research/100bit-spend-path-20261013/lean')]
seen={}
def visit(m):
 if m in seen:return
 rel=m.replace('.','/')+'.lean'
 p=next((r/rel for r in roots if (r/rel).is_file()),None)
 seen[m]=p
 if p:
  for line in p.read_text().splitlines():
   if line.startswith('import '):
    for d in line[7:].split():visit(d)
for m in sys.argv[1:]:visit(m)
script='from pathlib import Path; import json; roots='+repr([B+'/LPm_objects',C,C+'/objects','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'])+'; modules='+repr(list(seen))+'; print(json.dumps({m:next((str(Path(r)/(m.replace(".","/")+".olean")) for r in roots if (Path(r)/(m.replace(".","/")+".olean")).is_file()),None) for m in modules}))'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],capture_output=True,text=True,check=True);objects=json.loads(r.stdout)
order=[];done=set()
def missing(m):
 if m in done or objects[m]:return
 done.add(m);p=seen[m]
 if not p:raise SystemExit('STOP missing immutable source '+m)
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for d in line[7:].split():missing(d)
 order.append({'module':m,'source':str(p)})
for m in sys.argv[1:]:missing(m)
(E/'LPm_DEPENDENCIES.json').write_text(json.dumps({'targets':sys.argv[1:],'missing':order,'selected_existing':{m:v for m,v in objects.items() if v}},indent=2)+'\n')
print('Missing unchanged modules',len(order),flush=True)
for item in order:
 ids=[int(p.parent.name.removeprefix('LPm_L')) for p in E.glob('LPm_L*/receipt.json')]
 number=max(ids,default=0)+1
 assert len(ids)<80,'STOP Lean budget exhausted'
 a=f'LPm_L{number:03d}'
 r=subprocess.run([sys.executable,str(E/'LPm_lean.py'),a,item['source'],item['module']],capture_output=True,text=True)
 print(r.stdout[-1300:],flush=True)
 if r.returncode:raise SystemExit('STOP launcher failure '+a+' '+r.stderr)
 if json.loads((E/a/'receipt.json').read_text())['exit_status']!=0:raise SystemExit('STOP focused dependency '+item['module'])
