"""Preflight direct source import closure, copy missing objects from pinned supplier paths."""
from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent
tracked=subprocess.check_output(['git','ls-files','*.lean'],text=True).splitlines()
index={}
for s in tracked:
 p=Path(s)
 if '/sources/' in s or '/NNH_dependency_inputs/' in s:continue
 index.setdefault(p.stem,[]).append(s)
queue=['LIB_Instances','LIBB_V2Star','LIBB_PoolLib'];seen=set();provenance=[]
while queue:
 m=queue.pop()
 if m in seen:continue
 seen.add(m)
 candidates=index.get(m,[])
 if len(candidates)!=1:continue
 s=candidates[0];p=Path(s)
 data=p.read_text() if p.exists()else subprocess.check_output(['git','show','HEAD:'+s],text=True)
 provenance.append(dict(module=m,source=s,sha256=hashlib.sha256(data.encode()).hexdigest()))
 queue.extend(re.findall(r'^import\s+([\w.]+)',data,re.M))
paths=json.load(open('evidence/libb-20261111/LIBB_L344/receipt.json'))['env']['LEAN_PATH'].split(':')
code='''from pathlib import Path
import json,shutil,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-integrate-20261111');own=[b/'NNH_objects',b/'NNH_seed',b/'NNH_library_seed'];out=[];missing=[]
assert shutil.disk_usage(b).free>=40_000_000_000
for m in sorted(modules):
 rel=m.replace('.','/')+'.olean'
 if any((p/rel).is_file() for p in own):continue
 src=next((Path(p)/rel for p in paths if (Path(p)/rel).is_file()),None)
 if src is None:missing.append(m);continue
 for p,suffix in [(src,''),(Path(str(src)+'.private'),'.private'),(Path(str(src)+'.server'),'.server'),(src.with_suffix('.ir'),'IR')]:
  if not p.exists():continue
  q=own[1]/(rel[:-6]+'.ir' if suffix=='IR'else rel+suffix);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  out.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
print(json.dumps(dict(copied=out,missing=missing)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='modules='+repr(seen)+'\npaths='+repr(paths)+'\n'+code,capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);x['source_closure']=provenance;(E/'NNH_RESUME_PREFLIGHT.json').write_text(json.dumps(x,indent=2)+'\n');print('closure',len(seen),'copied',len(x['copied']),'missing',x['missing'])
