from pathlib import Path
import json,subprocess,sys,lzma,hashlib,base64
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NHP_frozen_identity import frozen,apply
files=dict(frozen());files.update({n:v.encode() for n,v in json.loads((E/'NHP_INCLUDES.json').read_text()).items()})
apply(files,(E/'NHP_KMX_copy_stubs.patch').read_text())
raw=json.dumps({n:base64.b64encode(v).decode() for n,v in files.items()}).encode();(E/'NHP_NATIVE_SEED.json.xz').write_bytes(lzma.compress(raw));(E/'NHP_NATIVE_SEED.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
B='/home/dombarker/project-offloads/codex-cx-pool-b3-20261106';H='dombarker@100.108.41.90'
code='''from pathlib import Path
import subprocess,json,sys,lzma,hashlib,base64
b=Path(B);b.mkdir(exist_ok=True);q=b/'NHP_NATIVE_SEED-admission.json'
with (b/'NHP_NATIVE_SEED-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
a=json.loads(q.read_text());print(json.dumps(dict(admission=a,exit=r.returncode)),flush=True)
if r.returncode or a.get('allowed') is not True:sys.exit(78)
s=b/'NHP_src';s.mkdir(exist_ok=True);total=0
for n,t in files.items():
 t=base64.b64decode(t);p=s/n;p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==t,n
 else:p.write_bytes(t)
 total+=len(t)
(b/'NHP_tmp').mkdir(exist_ok=True)
import shutil
for name in ['S2W_run_host.py','S2W_lean_host.py']:
 origin=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')/name
 target=b/name
 shutil.copy2(origin,target)
 assert origin.read_bytes()==target.read_bytes()
(b/'NHP_SEED.json').write_text(json.dumps(dict(files=len(files),seed_bytes=total,cache_bytes_copied=0,cache='/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104',launcher_reused=True)))
print(json.dumps(dict(files=len(files),bytes=total)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nfiles='+repr({n:base64.b64encode(v).decode() for n,v in files.items()})+'\n'+code,text=True,capture_output=True);(E/'NHP_NATIVE_SEED.log').write_text(r.stdout+r.stderr);print(r.stdout,r.stderr[-1500:]);assert r.returncode==0
