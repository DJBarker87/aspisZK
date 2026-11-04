from pathlib import Path
import subprocess,json,lzma,time,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ledger8-20261105';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104'
files=json.loads(lzma.decompress((E/'NGJ_POOL_SEED.json.xz').read_bytes()))
code='''from pathlib import Path
import subprocess,json,sys,shutil,hashlib,lzma,os
b=Path(B);c=Path(C);b.mkdir(exist_ok=True);c.mkdir(exist_ok=True)
with (b/'NGJ_POOL_SEED_RESERVATION.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NGJ_POOL_SEED_RESERVATION.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NGJ_POOL_SEED_RESERVATION.json').read_text());print(json.dumps(dict(admission=a,exit=r.returncode)),flush=True)
if r.returncode or a.get('allowed') is not True:sys.exit(78)
seen={};out=[]
for f in files:
 p=Path(f['source']);q=c/f['relative'];q.parent.mkdir(parents=True,exist_ok=True)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'],str(p)
 key=(f['sha256'],f['bytes'])
 if not q.exists():
  if key in seen:os.link(seen[key],q)
  else:shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==f['sha256'],str(q)
 seen[key]=q;out.append(dict(f,destination=str(q)))
raw=json.dumps(dict(selected=out,paths=len(out),bytes=sum(f['bytes'] for f in files),unique_bytes=sum(k[1] for k in seen))).encode()
(b/'NGJ_POOL_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(b/'NGJ_POOL_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
print(json.dumps(dict(paths=len(out),unique_bytes=sum(k[1] for k in seen))))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nfiles='+repr(files)+'\n'+code,text=True,capture_output=True)
 (E/('NGJ_POOL_SEED_TRANSPORT_'+str(retry)+'.log')).write_text(r.stdout+r.stderr);print(r.stdout[-1800:],flush=True)
 if r.returncode==0:break
 if r.returncode not in [78,255] or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
for n in ['NGJ_POOL_CACHE_IMPORTS.json.xz','NGJ_POOL_CACHE_IMPORTS.json.sha256','NGJ_POOL_SEED_RESERVATION.json','NGJ_POOL_SEED_RESERVATION.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
