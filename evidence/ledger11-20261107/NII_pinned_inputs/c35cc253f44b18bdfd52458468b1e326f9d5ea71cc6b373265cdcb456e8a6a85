from pathlib import Path
import json,subprocess,hashlib,time,shutil
E=Path(__file__).resolve().parent;U=E.parent/'prepared-claim-20261105';B='/home/dombarker/project-offloads/codex-cx-prepared-claim2-20261105';H='dombarker@100.108.41.90'
# Reuse unchanged retained NGU scratch as READ-ONLY source, no duplicate corpus transport.
code='''from pathlib import Path
import json,subprocess,sys,shutil,hashlib
b=Path(B); b.mkdir(exist_ok=True)
with (b/'NGY_SETUP_RESERVATION.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NGY_SETUP_RESERVATION.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NGY_SETUP_RESERVATION.json').read_text());print(json.dumps(dict(exit=r.returncode,reservation=a)),flush=True)
if r.returncode or a.get('allowed') is not True:sys.exit(78)
u=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-20261105');c=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104');rows=[]
for name in ['NGU_exports_20261105','NGK_exports_20261105']:
 for p in (c/name).rglob('*'):
  if p.is_file():rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(u/n,b/n)
for n in ['NGY_objects','NGY_generated','NGY_tmp','NGY_native']:(b/n).mkdir(exist_ok=True)
s=b/'NGY_src'
if not s.exists():shutil.copytree(u/'NGU_src',s)
# Restore frozen files modified by preceding own job before installing NGY patch.
for n,t in restore.items():(s/n).write_text(t)
for p in s.rglob('NGU_stages.rs'):p.unlink()
x=dict(imported=rows,bytes=sum(r['bytes'] for r in rows),paths=len(rows),cache_mode='retained own cache; hashed in place, no duplicate objects')
(b/'NGY_SEED.json').write_text(json.dumps(x,indent=1));print(json.dumps(dict(bytes=x['bytes'],paths=x['paths'])))
'''
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
restore={n:subprocess.check_output(['git','show',rev+':'+n],text=True) for n in ['crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/lib.rs']}
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nrestore='+repr(restore)+'\n'+code,text=True,capture_output=True)
 (E/f'NGY_SETUP_{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode not in [78,255] or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
for n in ['NGY_SEED.json','NGY_SETUP_RESERVATION.json','NGY_SETUP_RESERVATION.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
paths=json.loads((U/'NGU_PATHS.json').read_text());C='/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104'
paths=[B+'/NGY_objects',C+'/NGU_exports_20261105']+[p for p in paths if '/NGU_objects' not in p]
(E/'NGY_PATHS.json').write_text(json.dumps(paths,indent=1)+'\n')
print('seeded',json.loads((E/'NGY_SEED.json').read_text())['bytes'])
