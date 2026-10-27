from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
remote='''from pathlib import Path
import json,hashlib
c=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025');r=Path('/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz_sources')
seen=set();out=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 if any((p/(m.replace('.','/')+'.olean')).exists() for p in [c,c/'objects']):return
 p=r/(m.replace('.','/')+'.lean')
 if not p.exists():raise RuntimeError('missing selected source '+m)
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():visit(dep)
 out.append(dict(module=m,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source=p.read_text()))
visit('Op4P_Cuts')
print(json.dumps(out))'''
r=subprocess.run(['ssh',H,'python3 -'],input=remote,text=True,capture_output=True)
if r.returncode: raise SystemExit(r.stderr)
plan=json.loads(r.stdout)
for item in plan:
 p=E/'XRn_prerequisites'/ (item['module']+'.lean.txt');p.parent.mkdir(exist_ok=True);p.write_text(item.pop('source'))
 item['snapshot']=str(p.relative_to(E))
(E/'XRn_op4_plan.json').write_text(json.dumps(plan,indent=2)+'\n')
