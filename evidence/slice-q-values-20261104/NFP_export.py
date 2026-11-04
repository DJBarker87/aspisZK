"""Copy accepted private artifacts into the retained own cache; no compilation."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
modules=json.loads((E/'NFP_AUDIT_ROOTS.json').read_text())['modules']+['NFP_CombinedFinal','NFP_Driver','NFP_Scanner']
code='''from pathlib import Path
import shutil,json,hashlib,os
B=Path('/home/dombarker/project-offloads/codex-cx-slice-q-values-20261104')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-q-values-cache-20261104')
D=C/'NFP_exports_20261104'; D.mkdir(exist_ok=True)
modules=MODULES
files=[]
def copy(p,q):
 assert p.is_file(),str(p)
 h=hashlib.sha256(p.read_bytes()).hexdigest();q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,str(q)
 else:shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 files.append(dict(source=str(p),destination=str(q),sha256=h,bytes=p.stat().st_size))
for m in modules:
 copy(B/'NFP_generated'/(m+'.lean'),D/'sources'/(m+'.lean'))
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NFP_objects'/(m+suffix)
  if suffix=='.olean' or p.exists():copy(p,D/(m+suffix))
for m in ['NFP_Driver','NFP_Scanner']:
 copy(B/'NFP_native'/m,D/'audit-binaries'/m)
for m in ['NFP_Driver','NFP_Scanner','NFA_WALKER','NFA_MemoryLimit']:
 copy(B/'NFP_native'/(m+'.c'),D/'audit-native'/(m+'.c'))
manifest=dict(cache_retained=True,own_cache=str(C),export=str(D),files=files,no_key_cleanup=True,no_process_launch=True)
p=D/'NFP_EXPORT.json';p.write_text(json.dumps(manifest,indent=2)+'\\n');print(json.dumps(manifest))
'''.replace('MODULES',repr(modules))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NFP_EXPORT.log').write_text(r.stderr);assert r.returncode==0,r.stderr
manifest=json.loads(r.stdout);(E/'NFP_EXPORT.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(dict(files=len(manifest['files']),bytes=sum(x['bytes'] for x in manifest['files']),export=manifest['export'])))
