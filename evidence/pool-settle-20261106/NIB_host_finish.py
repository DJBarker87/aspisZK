"""Export small owned objects, then remove only hash-verified rebuildable outputs."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import hashlib,json,shutil,os
B=Path('/home/dombarker/project-offloads/codex-cx-pool-settle-20261106')
C=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIB_exports_20261106')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
C.mkdir(exist_ok=True);exports=[];removed=[]
for p in (B/'NIB_objects').glob('*'):
 assert p.is_file() and p.name.startswith('NIB_'),str(p)
 dest=C/p.name
 if dest.exists():assert sha(dest)==sha(p)
 else:shutil.copy2(p,dest)
 exports.append(dict(path=str(dest),sha256=sha(dest),bytes=dest.stat().st_size))
 assert sha(dest)==sha(p)
 removed.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size,export=str(dest)));p.unlink()
for n in ['NIB_Driver','NIB_ProofDriver']:
 p=B/'NIB_native'/n
 if p.exists():removed.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size,reason='rebuildable optimized binary; sources and pins retained'));p.unlink()
active=[]
for p in Path('/proc').glob('[0-9]*/cmdline'):
 try:parts=p.read_bytes().decode().split('\\0')
 except (FileNotFoundError,PermissionError,ProcessLookupError):continue
 if parts and Path(parts[0]).name in ['lean','leanc','cargo','rustc','cbmc'] and any(str(B) in x or 'NIB_generated' in x for x in parts):active.append(parts)
assert not active,active
v=os.statvfs(B)
result=dict(exports=exports,export_bytes=sum(r['bytes'] for r in exports),removed_rebuildable=removed,removed_bytes=sum(r['bytes'] for r in removed),cache_retained=str(C.parent),workspace=str(B),active_owned_provers=active,host_free_bytes=v.f_bavail*v.f_frsize)
(B/'NIB_HOST_END.json').write_text(json.dumps(result,indent=1)+'\\n');print(json.dumps(result))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NIB_HOST_END_TRANSPORT.log').write_text(r.stderr);assert r.returncode==0,(r.returncode,r.stderr)
(E/'NIB_HOST_END.json').write_text(json.dumps(json.loads(r.stdout),indent=1)+'\n')
x=json.loads(r.stdout);print(json.dumps({k:x[k] for k in ['export_bytes','removed_bytes','active_owned_provers','host_free_bytes']}))
