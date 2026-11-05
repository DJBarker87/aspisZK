"""Retain successful own objects; never rebuild or remove shared cache entries."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-d-finish3-20261106'
C='/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104'
modules=sorted({r['module'] for p in E.glob('NHE_L[0-9][0-9][0-9]/receipt.json') for r in [json.loads(p.read_text())] if r['kind']=='lean' and r['exit_status']==0 and r['module'].startswith('NHE_')})
code='''from pathlib import Path
import json,hashlib,shutil,subprocess,sys
b=Path(B);c=Path(C);out=c/'NHE_exports_20261106'
r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHE_EXPORT-reservation.json')],capture_output=True,text=True)
ad=json.loads((b/'NHE_EXPORT-reservation.json').read_text());assert r.returncode==0 and ad.get('allowed') is True,(r.returncode,ad)
files=[]
def copy(p,q):
 assert p.is_file(),str(p)
 q.parent.mkdir(parents=True,exist_ok=True)
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 else:shutil.copy2(p,q)
 files.append(dict(path=str(q.relative_to(out)),bytes=q.stat().st_size,sha256=h,source=str(p)))
for m in modules:
 p=b/'NHE_objects'/(m+'.olean');copy(p,out/'objects'/p.name)
 for suffix in ['.olean.private','.olean.server','.ir']:
  p=b/'NHE_objects'/(m+suffix)
  if p.exists():copy(p,out/'objects'/p.name)
 p=b/'NHE_generated'/(m+'.lean')
 if p.exists():copy(p,out/'sources'/p.name)
for n in ['NHE_Driver','NHE_ProofDriver']:copy(b/'NHE_native'/n,out/'native'/n)
manifest=dict(export=str(out),files=files,count=len(files),bytes=sum(f['bytes']for f in files),admission=dict(exit=r.returncode,reservation=ad),excluded=['NHE_ScalarStep'],never_delete_cache=True)
(out/'NHE_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\\n');print(json.dumps(manifest))
'''
code='B='+repr(B)+'\nC='+repr(C)+'\nmodules='+repr(modules)+'\n'+code
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,(r.returncode,r.stderr,r.stdout)
v=json.loads(r.stdout);(E/'NHE_EXPORT.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps({k:v[k] for k in ['export','count','bytes']}))
