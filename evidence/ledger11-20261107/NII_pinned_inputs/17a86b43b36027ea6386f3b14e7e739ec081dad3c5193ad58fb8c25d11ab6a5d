from pathlib import Path
import subprocess,json,time,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-d-entry2-20261106';H='dombarker@100.108.41.90'
code='''from pathlib import Path
import subprocess,json,sys,shutil,hashlib
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NHD_SEED-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHD_SEED-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NHD_SEED-reservation.json'
if not p.exists():print('MISSING');sys.exit(79)
a=json.loads(p.read_text());print(json.dumps(dict(exit=r.returncode,reservation=a)),flush=True)
if r.returncode or a.get('allowed') is not True:sys.exit(78)
src=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-20261105')
s=b/'NHD_src'
if not s.exists():shutil.copytree(src/'NGL_src',s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
exports=EXPORTS;rows=[]
for f in exports['files']:
 p=Path(exports['cache'])/f['relative'];assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'];rows.append(f)
for d in ['NHD_objects','NHD_tmp']:(b/d).mkdir(exist_ok=True)
result=dict(exports_cache=exports['cache'],imported_files=rows,imported_bytes=sum(f['bytes'] for f in rows),scratch_bytes=sum(p.stat().st_size for p in s.rglob('*') if p.is_file()),cache_policy='Existing retained lane cache reused read-only; no deletion; NHD new objects private')
(b/'NHD_SEED.json').write_text(json.dumps(result,indent=1));print(json.dumps({k:v for k,v in result.items() if k!='imported_files'}))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nEXPORTS='+repr(json.loads((E.parent/'slice-d-entry-20261105/NGL_EXPORTS.json').read_text()))+'\n'+code,capture_output=True,text=True)
 (E/f'NHD_SEED-fixed-transport-{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout,flush=True)
 if r.returncode==0:break
 if retry<10 and r.returncode in [78,255]:time.sleep(60 if r.returncode==255 else 180);continue
 if retry==0 and r.returncode==79:time.sleep(30);continue
 raise SystemExit(r.returncode)
for n in ['NHD_SEED.json','NHD_SEED-reservation.json','NHD_SEED-barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
