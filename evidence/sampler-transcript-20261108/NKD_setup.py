from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-sampler-transcript-20261108';C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NKD_20261108'
seeds=[]
code='''from pathlib import Path
import json,subprocess,sys,hashlib,shutil,lzma
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NKD_seed-admission.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NKD_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NKD_seed-admission.json'
if not p.exists():sys.exit(79)
a=json.loads(p.read_text())
if r.returncode or a.get('allowed')is not True:print(json.dumps(dict(exit=r.returncode,reservation=a)));sys.exit(78)
c=Path(C);c.mkdir(exist_ok=True);rows=[]
for tag,root in [('NKC','/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKC_20261108/NKC_exports_20261108'),('NIX','/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104/NIX_exports_20261107')]:
 root=Path(root)
 for p in sorted(root.rglob('*')):
  if p.is_file():seeds.append(dict(tag=tag,path=str(p),relative=str(p.relative_to(root)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
for row in seeds:
 p=Path(row['path']);assert p.is_file(),str(p)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
 q=c/(row['tag']+'_seed')/row['relative'];q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==row['sha256']
 rows.append(dict(row,destination=str(q)))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
x=dict(files=rows,bytes=sum(Path(r['destination']).stat().st_size for r in rows),admission=a,exit=r.returncode,disk=shutil.disk_usage(b)._asdict())
(b/'NKD_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x).encode()));print(json.dumps(dict(files=len(rows),bytes=x['bytes'],disk=x['disk'])))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nseeds='+repr(seeds)+'\n'+code,text=True,capture_output=True)
 (E/f'NKD_seed-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode in[78,255,79]and retry<10:time.sleep(180 if r.returncode==78 else 60 if r.returncode==255 else 30);continue
 raise RuntimeError(r.stdout[-1000:]+r.stderr)
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat '+B+'/NKD_CACHE_IMPORTS.json.xz'],capture_output=True);assert r.returncode==0;(E/'NKD_CACHE_IMPORTS.json.xz').write_bytes(r.stdout)
print('NJK seed copied and hash checked')
