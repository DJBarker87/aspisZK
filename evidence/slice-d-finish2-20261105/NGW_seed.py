from pathlib import Path
import json,lzma,subprocess,time
E=Path(__file__).resolve().parent; H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-slice-d-finish2-20261105'; C='/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104'
x=json.loads(lzma.decompress((E.parent/'pool-retarget-20261105/NGK_CLOSURE_PINS.json.xz').read_bytes()))
exports={r['path'].split('/NGK_objects/')[-1]:r for r in json.loads((E.parent/'pool-retarget-20261105/NGK_EXPORT.json').read_text())['exports']}
remote='''from pathlib import Path
import json,sys,subprocess,hashlib,shutil,lzma
b=Path(B);c=Path(C);b.mkdir(exist_ok=True)
with (b/'NGW_SEED-admission.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NGW_SEED-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NGW_SEED-admission.json';print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists():sys.exit(79)
if r.returncode or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
selected=[];copied=0
for f in x['selected_objects']:
 p=Path(f['path']);root=next(z for z in x['LEAN_PATH'] if str(p).startswith(z+'/'));rel=str(p)[len(root)+1:]
 if '/.elan/' in str(p):continue
 if '/NGK_objects/' in str(p):p=Path('/home/dombarker/project-offloads/codex-cx-pool-retarget-cache-20261104/NGK_exports_20261105')/rel
 if not p.exists() and '/NGJ_objects/' in str(p):p=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGJ_exports_20261105')/rel
 data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==f['sha256'],str(p)
 q=c/rel
 if q.exists() and hashlib.sha256(q.read_bytes()).hexdigest()!=f['sha256']:q=c/'NGW_NGK_seed'/rel
 if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data);copied+=len(data)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==f['sha256']
 selected.append(dict(f,source=str(p),destination=str(q)))
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')/n,b/n)
raw=json.dumps(dict(selected=selected,bytes=sum(z['bytes'] for z in selected),files=len(selected),copied_bytes=copied,NGM_exports='/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104/NGM_exports_20261105')).encode()
(b/'NGW_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(b/'NGW_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
print(json.dumps(dict(files=len(selected),bytes=sum(z['bytes'] for z in selected),copied_bytes=copied)))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nx='+repr(x)+'\n'+remote,text=True,capture_output=True)
 (E/f'NGW_SEED-{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout[-1000:],r.stderr[-1000:],flush=True)
 if not r.returncode:break
 if r.returncode not in [78,79,255] or retry==10:raise SystemExit(r.returncode)
 time.sleep(30 if r.returncode==79 else 60 if r.returncode==255 else 180)
for n in ['NGW_CACHE_IMPORTS.json.xz','NGW_CACHE_IMPORTS.json.sha256','NGW_SEED-admission.json','NGW_SEED-admission.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert not r.returncode;(E/n).write_bytes(r.stdout)
