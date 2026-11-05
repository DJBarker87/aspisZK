from pathlib import Path
import subprocess,json,hashlib,sys,time
E=Path(__file__).resolve().parent; H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads/codex-cx-slice-d-entry3-20261106'
code='''from pathlib import Path
import subprocess,json,sys,shutil,hashlib
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NHJ_SEED-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHJ_SEED-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NHJ_SEED-reservation.json'
if not p.exists():print('MISSING');sys.exit(79)
a=json.loads(p.read_text());print(json.dumps(dict(exit=r.returncode,reservation=a)),flush=True)
if r.returncode or a.get('allowed') is not True:sys.exit(78)
src=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry2-20261106')
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
s=b/'NHJ_src'
if not s.exists():shutil.copytree(src/'NHD_src',s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
for n in ['NHJ_objects','NHJ_tmp']:(b/n).mkdir(exist_ok=True)
rows=[]
for x in exports['exports']:
 p=Path(x['destination']);assert hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256'];rows.append(x)
result=dict(imported_files=rows,imported_bytes=sum(x['bytes'] for x in rows),scratch_bytes=sum(p.stat().st_size for p in s.rglob('*') if p.is_file()),cache_policy='NHD/NGL/NGK retained exports read-only in existing lane cache; NHJ objects private, cache never deleted',disk=subprocess.check_output(['df','-h','/'],text=True))
(b/'NHJ_SEED.json').write_text(json.dumps(result,indent=1));print(json.dumps({k:v for k,v in result.items() if k!='imported_files'}))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nexports='+repr(json.loads((E.parent/'slice-d-entry2-20261106/NHD_EXPORTS.json').read_text()))+'\n'+code,capture_output=True,text=True)
 (E/f'NHJ_SEED-transport-{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout,flush=True)
 if r.returncode==0:break
 if retry<10 and r.returncode in [78,255]:time.sleep(60 if r.returncode==255 else 180);continue
 if retry==0 and r.returncode==79:time.sleep(30);continue
 raise SystemExit(r.returncode)
for n in ['NHJ_SEED.json','NHJ_SEED-reservation.json','NHJ_SEED-barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
