"""Export only this job's checked objects/binaries; preserve all retained caches."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-d-pair2-20261106';C='/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104';H='dombarker@100.108.41.90'
modules=sorted({r['module']for p in E.glob('NHM_L[0-9][0-9][0-9]/receipt.json')for r in[json.loads(p.read_text())]if r['kind']=='lean'and r['exit_status']==0})
code=r'''from pathlib import Path
import json,hashlib,shutil,subprocess,sys,os
b=Path(B);out=Path(C)/'NHM_exports_20261106'
with (b/'NHM_EXPORT-barrier.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHM_EXPORT-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NHM_EXPORT-admission.json'
if not p.exists():print('MISSING');sys.exit(79)
ad=json.loads(p.read_text())
if r.returncode or ad.get('allowed')is not True:print(json.dumps(dict(exit=r.returncode,reservation=ad)));sys.exit(78)
files=[]
def copy(p,q):
 assert p.is_file(),str(p)
 data=p.read_bytes();h=hashlib.sha256(data).hexdigest();q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 else:shutil.copy2(p,q)
 files.append(dict(path=str(q.relative_to(out)),source=str(p),sha256=h,bytes=len(data)))
for m in modules:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=b/'NHM_objects'/(m+suffix)
  if p.exists():copy(p,out/'objects'/p.name)
 copy(b/'NHM_generated'/(m+'.lean'),out/'sources'/(m+'.lean'))
for n in ['NHM_Driver','NHM_ProofDriver']:copy(b/'NHM_native'/n,out/'native'/n)
manifest=dict(export=str(out),count=len(files),bytes=sum(r['bytes']for r in files),files=files,admission=dict(exit=r.returncode,reservation=ad),never_delete_cache=True)
(out/'NHM_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit()or int(p.name)==os.getpid():continue
 try:cwd=str((p/'cwd').resolve());args=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
 except(OSError,PermissionError):continue
 if cwd.startswith(str(b))and any(x in args for x in ['lean','kani','rustc','cbmc','S2W_run_host','NHM_audit_batch']):active.append(dict(pid=p.name,args=args))
assert not active,active
removed=[]
for name in ['NHM_target','NHM_ref_target','NHM_objects','NHM_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
for name in ['NHM_Driver','NHM_ProofDriver','NGW_Driver','NGW_ProofDriver']:
 p=b/'NHM_native'/name
 if p.exists():p.unlink();removed.append(str(p))
cleanup=dict(active_formal_processes=active,removed_rebuildable_only=removed,retained_cache=str(out),cache_deleted=False,keys_handled=False,disk=subprocess.check_output(['df','-h',str(b)],text=True))
(b/'NHM_CLEANUP.json').write_text(json.dumps(cleanup,indent=2)+'\n')
print(json.dumps(dict(manifest=manifest,cleanup=cleanup)))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nmodules='+repr(modules)+'\n'+code,text=True,capture_output=True)
 (E/f'NHM_EXPORT-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:
  x=json.loads(r.stdout);(E/'NHM_EXPORT.json').write_text(json.dumps(x['manifest'],indent=2)+'\n');(E/'NHM_CLEANUP.json').write_text(json.dumps(x['cleanup'],indent=2)+'\n');print(json.dumps({k:x['manifest'][k]for k in['export','count','bytes']}));break
 if r.returncode not in[78,79,255]or retry==10:raise SystemExit(r.returncode)
 print('reservation/transport wait',r.returncode,flush=True);time.sleep(30 if r.returncode==79 else 60 if r.returncode==255 else 180)
