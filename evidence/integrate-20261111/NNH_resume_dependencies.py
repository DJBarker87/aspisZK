"""Copy missing selected closure objects only, with bounded manifest enumeration."""
from pathlib import Path
import json,lzma,subprocess
E=Path(__file__).resolve().parent
x=json.loads(lzma.open('evidence/lib-20261111/LIB_BUNDLE_CLOSURE_PINS.json.xz').read())
rows=x['selected_modules']
y=json.loads(lzma.open('evidence/libb-20261111/LIBB_RESUME_PINS.json.xz').read())
for r in y['objects']:
 if r['path'].endswith('.olean'):
  name=Path(r['path']).stem
  if name.startswith(('NMT_','NMS_','LIB','NND_','NNC_')):rows.append(dict(r,module=name))
code='''from pathlib import Path
import hashlib,shutil,json
b=Path('/home/dombarker/project-offloads/codex-cx-integrate-20261111');roots=[b/'NNH_objects',b/'NNH_seed',b/'NNH_library_seed'];out=[]
assert shutil.disk_usage(b).free>=40_000_000_000
for r in rows:
 rel=r['module'].replace('.','/')+'.olean'
 if any((root/rel).is_file() for root in roots):continue
 p=Path(r['path']);h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==r['sha256'],str(p)
 for src,suffix in [(p,''),(Path(str(p)+'.private'),'.private'),(Path(str(p)+'.server'),'.server'),(p.with_suffix('.ir'),'IR')]:
  if not src.exists():continue
  dst=roots[1]/(rel[:-6]+'.ir' if suffix=='IR' else rel+suffix);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
  out.append(dict(source=str(src),destination=str(dst),sha256=hashlib.sha256(dst.read_bytes()).hexdigest()))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='rows='+repr(rows)+'\n'+code,capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'NNH_RESUME_DEPENDENCY_IMPORTS.json').write_text(r.stdout);print('copied',len(json.loads(r.stdout)))
