from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-poseidon-state-20261108'
C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NKG_20261108'
code='''from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NKG_seed-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NKG_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NKG_seed-admission.json'
if not p.exists():print('MISSING');sys.exit(79)
a=json.loads(p.read_text())
if r.returncode!=0 or a.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,reservation=a)));sys.exit(78)
c=Path(C);c.mkdir(exist_ok=True);rows=[]
for tag,src in [('NKC','/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKC_20261108/NKC_exports_20261108'),('NJP','/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJP_20261108/NJP_exports_20261108')]:
 for p in sorted(Path(src).rglob('*')):
  if not p.is_file():continue
  q=c/(tag+'_seed')/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if not q.exists():shutil.copy2(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  rows.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 q=b/n
 if not q.exists():shutil.copy2(w/n,q)
(b/'NKG_objects').mkdir(exist_ok=True);(b/'NKG_tmp').mkdir(exist_ok=True)
x=dict(admission=a,exit=r.returncode,files=rows,bytes=sum(r['bytes'] for r in rows),disk=shutil.disk_usage(b)._asdict())
(b/'NKG_SEED.json').write_text(json.dumps(x,indent=2));print(json.dumps(x))
'''
for n in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nC='+repr(C)+'\n'+code,text=True,capture_output=True)
 (E/f'NKG_seed-transport-{n}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:
  x=json.loads(r.stdout);(E/'NKG_SEED.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(files=len(x['files']),bytes=x['bytes'],free=x['disk']['free'])));break
 if r.returncode in [78,79,255] and n<10:time.sleep(180 if r.returncode==78 else 60 if r.returncode==255 else 30);continue
 raise RuntimeError(r.stdout[-2000:]+r.stderr)
