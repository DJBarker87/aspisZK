from pathlib import Path
import subprocess,json,hashlib,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-d-pair3-20261106'
H='dombarker@100.108.41.90'
P='/home/dombarker/project-offloads/codex-cx-slice-d-finish3-20261106'
C='/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104'
# Copy retained exports only; no source or object in another workspace is modified.
files={}
manifest=json.loads((E.parent/'slice-d-pair2-20261106/NHM_EXPORT.json').read_text());manifest['files_manifest']=manifest['files'];manifest['path']=manifest['export']
code='''from pathlib import Path
import subprocess,json,sys,hashlib,shutil
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NHX_SETUP-barrier.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHX_SETUP-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NHX_SETUP-admission.json';print(p.read_text()if p.exists()else'MISSING',flush=True)
if not p.exists():sys.exit(79)
if r.returncode or json.loads(p.read_text()).get('allowed')is not True:sys.exit(78)
pins=[]
for row in manifest['files_manifest']:
 p=Path(manifest['path'])/row['path'];assert p.stat().st_size==row['bytes'];assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'];pins.append(dict(row,source=str(p)))
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 p=Path(P)/n;shutil.copy2(p,b/n)
for n in ['NHX_objects','NHX_generated','NHX_tmp','NHX_native']:(b/n).mkdir(exist_ok=True)

shutil.copytree('/home/dombarker/project-offloads/codex-cx-slice-d-pair2-20261106/NHM_src',b/'NHX_src',dirs_exist_ok=True)
for n,t in files.items():(b/n).write_text(t)
(b/'NHX_SEED.json').write_text(json.dumps(dict(files=len(pins),bytes=sum(p['bytes']for p in pins),copies='retained export files hash-checked and reused read-only; no retained binary or object copied; own audit drivers built privately',pins=pins),indent=2))
print('SETUP_OK')
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nP='+repr(P)+'\nfiles='+repr(files)+'\nmanifest='+repr(manifest)+'\n'+code,capture_output=True,text=True)
 (E/f'NHX_SETUP-{retry}.log').write_text(r.stdout+r.stderr)
 print(r.stdout[-500:],r.stderr[-500:],flush=True)
 if r.returncode==0:break
 if r.returncode not in [78,79,255]or retry==10:raise SystemExit(r.returncode)
 time.sleep(30 if r.returncode==79 else 60 if r.returncode==255 else 180)
for n in ['NHX_SEED.json','NHX_SETUP-admission.json','NHX_SETUP-barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
