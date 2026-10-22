"""Install only missing retained circle dependencies, never overwrite a shared object."""
from pathlib import Path
import json,hashlib,shutil
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit22-20261021');J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
e=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text());paths=[J/'objects']+[Path(x) for x in e['LEAN_PATH'].split(':')]
headers=json.loads((H/'r4-module-headers.json').read_text())
index={r['path'].split('/r4-cache/')[-1].split('/objects/')[-1][:-6].replace('/','.'):r for r in headers}
seen=set();selected=[];missing=[]
def visit(m):
 if m in seen:return
 seen.add(m);rel=Path(m.replace('.','/')+'.olean')
 if any((d/rel).exists() for d in paths):return
 if m not in index:missing.append(m);return
 row=index[m];p=Path(row['path']);selected.append(dict(module=m,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,imports=row['imports']))
 for d in row['imports']:visit(d)
for m in ['AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyUnconditionalV1','AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCoordinatesV1']:visit(m)
assert not missing,missing
for row in selected:
 p=Path(row['path']);d=J/'objects'/Path(row['module'].replace('.','/')+'.olean')
 assert not d.exists()
 d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,d)
 row['installed']=str(d);row['sidecars']=[]
 for source,target in [(Path(str(p)+s),Path(str(d)+s)) for s in ['.private','.server']]+[(p.with_suffix('.ir'),d.with_suffix('.ir'))]:
  if source.exists():
   assert not target.exists();shutil.copy2(source,target)
   row['sidecars'].append(dict(path=str(target),sha256=hashlib.sha256(target.read_bytes()).hexdigest(),bytes=target.stat().st_size))
(H/'r4-installed-closure.json').write_text(json.dumps(dict(selected=selected,missing=missing,existing_objects_overwritten=0,source_files_overwritten=0),indent=2)+'\n')
print('Installed',len(selected),'retained dependencies; no existing source or object overwritten')
