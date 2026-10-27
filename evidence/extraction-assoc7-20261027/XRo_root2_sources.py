from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
remote='''from pathlib import Path
import json,hashlib
c=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025');r=Path('/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz5_sources')
seen=set();out=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 if any((p/(m.replace('.','/')+'.olean')).exists() for p in [Path('/home/dombarker/project-offloads/codex-cx-extraction-assoc7-20261027/XRo_objects'),c,c/'objects']):return
 p=next((root/(m.replace('.','/')+'.lean') for root in [r,r.parent/'RPz4_sources',r.parent/'RPz_sources'] if (root/(m.replace('.','/')+'.lean')).exists()),r/(m.replace('.','/')+'.lean'))
 if not p.exists():raise RuntimeError('missing selected source '+m)
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():visit(dep)
 out.append(dict(module=m,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source=p.read_text()))
visit('Op4P_Accepted')
print(json.dumps(out))'''
r=subprocess.run(['ssh',H,'python3 -'],input=remote,text=True,capture_output=True,check=True)
plan=json.loads(r.stdout)
for item in plan:
 p=E/'XRo_prerequisites'/ (item['module']+'.lean.txt');p.parent.mkdir(exist_ok=True);p.write_text(item.pop('source'))
 item['snapshot']=str(p.relative_to(E))
(E/'XRo_ROOT2_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
