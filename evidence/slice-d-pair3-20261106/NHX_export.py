"""Retain own current checked objects in own cache, never remove the cache."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
modules=sorted(p.stem for p in E.glob('NHX_*.lean'))
B='/home/dombarker/project-offloads/codex-cx-slice-d-pair3-20261106'
C='/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104/NHX_exports_20261106'
code=f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});d=Path({C!r});modules={modules!r}
assert not d.exists(), 'Do not overwrite retained exports'
(d/'objects').mkdir(parents=True);(d/'sources').mkdir()
files=[]
for m in modules:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=b/'NHX_objects'/(m+suffix)
  if p.exists():
   target=d/'objects'/p.name;shutil.copy2(p,target)
   files.append(dict(path=str(target),bytes=target.stat().st_size,sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
 p=b/'NHX_generated'/(m+'.lean');target=d/'sources'/p.name;shutil.copy2(p,target)
 files.append(dict(path=str(target),bytes=target.stat().st_size,sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
result=dict(destination=str(d),files=files,bytes=sum(f['bytes']for f in files),modules=len(modules),retained_cache=True,source_root=str(b),cleanup_targets=[])
(d/'MANIFEST.json').write_text(json.dumps(result,indent=2)+'\\n');print(json.dumps(result))
'''
# One submission only: recover read-only if transport fails after this mutation.
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NHX_EXPORT_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr,submitted=True))+'\n')
assert r.returncode==0,'recover read-only; never resubmit'
data=json.loads(r.stdout);(E/'NHX_EXPORT.json').write_text(json.dumps(data,indent=2)+'\n');print(data['modules'],data['bytes'])
