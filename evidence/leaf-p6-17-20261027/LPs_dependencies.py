"""Read-only dependency inventory; unchanged missing sources rebuilt privately."""
from pathlib import Path
import subprocess,json,sys,shlex,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-leaf-p6-17-20261027';C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';X='/home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027/XRw_objects'
roots=[Path('lean'),Path('docs/research/100bit-spend-path-20261013/lean'),Path('evidence/leaf-p6-10-20261027'),Path('evidence/leaf-p6-12-20261027')];seen={}
def visit(m):
 if m in seen:return
 rel=m.replace('.','/')+'.lean';p=next((r/rel for r in roots if (r/rel).is_file()),None);seen[m]=p
 if p:
  for line in p.read_text().splitlines():
   if line.startswith('import '):
    for d in line[7:].split():visit(d)
for m in sys.argv[1:]:visit(m)
script='from pathlib import Path; import json; roots='+repr(['/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027',X,C,C+'/objects','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'])+'; modules='+repr(list(seen))+'; print(json.dumps({m:next((str(Path(r)/(m.replace(".","/")+".olean")) for r in roots if (Path(r)/(m.replace(".","/")+".olean")).is_file()),None) for m in modules}))'
for retry in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90','python3 -'],input=script,capture_output=True,text=True)
 with (E/'LPs_DEPENDENCY_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))+'\n')
 if r.returncode==0:break
 if r.returncode!=255 or retry==10:raise SystemExit('STOP dependency inventory '+r.stderr)
 time.sleep(60)
objects=json.loads(r.stdout);order=[];done=set()
def missing(m):
 if m in done or objects[m]:return
 done.add(m);p=seen[m]
 if not p:raise SystemExit('STOP missing immutable source '+m)
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for d in line[7:].split():missing(d)
 order.append(dict(module=m,source=str(p)))
for m in sys.argv[1:]:missing(m)
p=E/('LPs_DEPENDENCIES_'+sys.argv[1]+'.json');p.write_text(json.dumps(dict(targets=sys.argv[1:],missing=order,selected_existing={m:v for m,v in objects.items() if v}),indent=2)+'\n')
print('Missing unchanged modules',len(order),flush=True)
