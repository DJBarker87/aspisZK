"""Read-only retained exports; create only NIO-owned host workspace."""
from pathlib import Path
import hashlib,json,subprocess,time,sys
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-pool-borrow2-20261107'
H='dombarker@100.108.41.90'
code='''from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path(B);b.mkdir(exist_ok=True)
q=b/'NIO_SEED_RESERVATION.json'
with (b/'NIO_SEED_BARRIER.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
if not q.exists():sys.exit(79)
ad=json.loads(q.read_text())
if r.returncode or ad.get('allowed') is not True:print(json.dumps(dict(admission=ad,exit=r.returncode)));sys.exit(78)
w=b.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copy2(w/n,b/n)
for n in ['NIO_tmp','NIO_objects','NIO_native','NIO_generated']:(b/n).mkdir(exist_ok=True)
old=b.parent/'codex-cx-pool-b4-20261107';stage=old/'NIE_stage'
(b/'NIO_stage').mkdir(exist_ok=True)
pins=[]
for p in stage.iterdir():
 if p.is_file() and p.name.startswith('NHR_'):
  z=b/'NIO_stage'/p.name;shutil.copy2(p,z)
  pins.append(dict(source=str(p),path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest(),bytes=z.stat().st_size))
rows=[]
for job,prefix in [('pool-borrow-20261107','NIK'),('pool-b4-20261107','NIE'),('pool-b3-20261106','NHP'),('pool-retarget-20261105','NGK')]:
 p=b.parent/('codex-cx-'+job)/(prefix+'_EXPORT.json')
 if not p.exists():raise RuntimeError('missing retained export '+str(p))
 doc=json.loads(p.read_text())
 for row in doc['exports']:
  z=Path(row['path']);assert z.is_file() and hashlib.sha256(z.read_bytes()).hexdigest()==row['sha256']
  rows.append(dict(path=str(z),sha256=row['sha256'],bytes=z.stat().st_size,copied=False))
report=dict(admission=ad,admission_exit=r.returncode,imports=rows,staging=pins,seed_bytes=sum(x['bytes'] for x in pins),object_bytes_copied=0,read_only_reused_bytes=sum(x['bytes'] for x in rows),disk_free=shutil.disk_usage(b).free)
(b/'NIO_CACHE_IMPORTS.json').write_text(json.dumps(report,indent=1))
print(json.dumps(report))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\n'+code,text=True,capture_output=True)
 (E/f'NIO_SEED_TRANSPORT_{retry}.log').write_text(r.stderr)
 if r.returncode==0:
  (E/'NIO_CACHE_IMPORTS.json').write_text(r.stdout)
  print('NIO seed pinned; '+str(json.loads(r.stdout)['seed_bytes'])+' input bytes; object copies 0');break
 if r.returncode in [255,78,79] and retry<10:time.sleep(60 if r.returncode==255 else 30 if r.returncode==79 else 180);continue
 print('NIO seed failed; exit '+str(r.returncode));sys.exit(r.returncode)
