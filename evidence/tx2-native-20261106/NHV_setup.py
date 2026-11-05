"""Private small seed, unchanged launcher, strict admission before uploads."""
from pathlib import Path
import subprocess,json,time,hashlib
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-tx2-native-20261106'
C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104'
code=f'''from pathlib import Path
import subprocess,json,sys,shutil,hashlib
b=Path({B!r});b.mkdir(exist_ok=True);p=b/'NHV_SETUP-admission.json'
with (b/'NHV_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists():sys.exit(79)
if r.returncode!=0 or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
w=b.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copyfile(w/n,b/n)
for n in ['NHV_objects','NHV_generated','NHV_tmp','NHV_native']:(b/n).mkdir(exist_ok=True)
c=Path({C!r})/'NHV_seed_20261106';c.mkdir(exist_ok=True)
records=[]
for p in sorted((Path({C!r})/'NHT_exports_20261106').glob('*')):
 if not p.is_file():continue
 q=c/p.name;shutil.copyfile(p,q);h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 records.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
(b/'NHV_SEED.json').write_text(json.dumps(records,indent=2))
print(json.dumps(dict(seed=records,bytes=sum(z['bytes'] for z in records),free=shutil.disk_usage(b).free)))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
 (E/f'NHV_SETUP-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:
  lines=r.stdout.splitlines();seed=json.loads(lines[-1]);(E/'NHV_SEED.json').write_text(json.dumps(seed,indent=2)+'\n');break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 if r.returncode==78 and retry<10:time.sleep(180);continue
 if r.returncode==79 and retry==0:time.sleep(30);continue
 raise RuntimeError('STOP setup infrastructure: '+r.stdout+r.stderr)
else:raise RuntimeError('STOP admission exhausted')
