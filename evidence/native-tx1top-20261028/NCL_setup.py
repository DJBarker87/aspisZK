from pathlib import Path
import subprocess,json,shlex,hashlib,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-native-tx1top-20261028'
C='/home/dombarker/project-offloads/codex-cx-tx1top-cache-20261028'
code='''from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NCL_SETUP-barrier.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NCL_SETUP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NCL_SETUP-reservation.json').read_text());print(json.dumps(dict(reservation=a,exit=r.returncode)),flush=True)
if r.returncode!=0 or a.get('allowed') is not True:sys.exit(78)
c=Path(C);c.mkdir(exist_ok=True);imports=[]
for origin in ['/home/dombarker/project-offloads/codex-cx-tx2mid-cache-20261028','/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027']:
 for p in sorted(Path(origin).rglob('*')):
  if not p.is_file():continue
  n=p.relative_to(origin);q=c/n;h=hashlib.sha256(p.read_bytes()).hexdigest()
  if q.exists():
   imports.append(dict(source=str(p),destination=str(q),sha256=h,selected=False,selected_sha256=hashlib.sha256(q.read_bytes()).hexdigest()));continue
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
  imports.append(dict(source=str(p),destination=str(q),sha256=h,selected=True,bytes=p.stat().st_size))
(b/'NCL_CACHE_IMPORTS.json').write_text(json.dumps(imports,indent=2)+'\\n')
base=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_lean_host.py','S2W_run_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:
 p=base/n
 if p.exists():
  q=b/n
  if q.exists():assert q.read_bytes()==p.read_bytes(),n
  else:shutil.copyfile(p,q)
print(json.dumps(dict(imports=imports,launchers={n:hashlib.sha256((b/n).read_bytes()).hexdigest() for n in ['S2W_lean_host.py','S2W_run_host.py']})))
'''
# Substitute only constant bindings, never interpret source as shell text.
code=code.replace('Path(B)',f'Path({B!r})').replace('Path(C)',f'Path({C!r})')
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
 (E/f'NCL_SETUP-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==255:
  if retry<10:time.sleep(60);continue
  raise SystemExit('transport exhausted')
 if r.returncode==78:
  if retry<10:print('admission refused; retry after 180s',flush=True);time.sleep(180);continue
  raise SystemExit('admission exhausted')
 assert r.returncode==0,r.stderr+r.stdout
 v=json.loads(r.stdout.splitlines()[-1]);(E/'NCL_CACHE_IMPORTS.json').write_text(json.dumps(v,indent=2)+'\n')
 print(json.dumps(dict(imported=len(v['imports']),launchers=v['launchers'])));break
