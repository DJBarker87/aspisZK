from pathlib import Path
import subprocess,json,sys,shutil,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-slice-d-entry5-20261107'
code="""from pathlib import Path
import subprocess,sys,json,shutil,hashlib
b=Path(B);b.mkdir(exist_ok=True)
p=b/'NIJ_SEED-reservation.json'
with (b/'NIJ_SEED-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
a=json.loads(p.read_text());print(json.dumps(dict(exit=r.returncode,reservation=a)),flush=True)
if r.returncode or a.get('allowed') is not True:sys.exit(78)
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
s=b/'NIJ_src';assert not s.exists()
shutil.copytree('/home/dombarker/project-offloads/codex-cx-slice-d-entry4-20261106/NHY_src',s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
for n in ['NIJ_objects','NIJ_tmp']:(b/n).mkdir(exist_ok=True)
cache=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104/NIJ_seed');cache.mkdir(exist_ok=True)
rows=[]
for r in exports['files']:
 src=Path(exports['directory'])/r['path'];assert hashlib.sha256(src.read_bytes()).hexdigest()==r['sha256']
 dst=cache/r['path'];dst.parent.mkdir(parents=True,exist_ok=True)
if True:
 for root in [Path(exports['directory']),Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104/NHJ_exports_20261106')]:
  for src in root.rglob('*'):
   if not src.is_file():continue
   dst=cache/src.relative_to(root);dst.parent.mkdir(parents=True,exist_ok=True)
   if dst.exists():assert dst.read_bytes()==src.read_bytes()
   else:shutil.copy2(src,dst)
   rows.append(dict(source=str(src),destination=str(dst),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),bytes=src.stat().st_size))
x=dict(files=rows,seed_bytes=sum(r['bytes'] for r in rows),scratch_bytes=sum(p.stat().st_size for p in s.rglob('*') if p.is_file()),disk=subprocess.check_output(['df','-h','/'],text=True))
(b/'NIJ_SEED.json').write_text(json.dumps(x,indent=1));print(json.dumps(dict(seed_bytes=x['seed_bytes'],scratch_bytes=x['scratch_bytes'],disk=x['disk'])))
"""
exports=json.loads((E.parent/'slice-d-entry4-20261106/NHY_CACHE_EXPORT.json').read_text())
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nexports='+repr(exports)+'\n'+code,capture_output=True,text=True)
(E/'NIJ_SEED-transport.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr);assert r.returncode==0
for n in ['NIJ_SEED.json','NIJ_SEED-reservation.json','NIJ_SEED-barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
