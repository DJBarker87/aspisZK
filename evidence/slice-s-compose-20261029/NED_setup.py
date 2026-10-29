from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-s-compose-20261029'
code='''from pathlib import Path
import subprocess,json,hashlib,sys
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NED_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NED_SETUP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NED_SETUP-reservation.json').read_text());print(json.dumps(dict(admission=a,exit=r.returncode)),flush=True)
if r.returncode!=0 or a.get('allowed') is not True:sys.exit(78)
c=b.parent/'codex-cx-slice-s-compose-cache-20261029';c.mkdir(exist_ok=True);imports=[]
for name in ['codex-cx-leaf-cache-20261027','codex-cx-cpilot-cache-20261028','codex-cx-front2-cache-20261028','codex-cx-front4-cache-20261028']:
 for p in sorted((b.parent/name).rglob('*')):
  if not p.is_file():continue
  q=c/p.relative_to(b.parent/name);h=hashlib.sha256(p.read_bytes()).hexdigest();copied=not q.exists()
  if copied:q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
  imports.append(dict(source=str(p),destination=str(q),sha256=h,selected_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),copied=copied))
coherent=b.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:(b/n).write_bytes((coherent/n).read_bytes())
for n in ['NED_generated','NED_objects']:(b/n).mkdir(exist_ok=True)
lib=[coherent/'objects/Aeneas.olean']+list((coherent/'objects/Aeneas').rglob('*.olean'))
print(json.dumps(dict(cache_imports=imports,library={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in lib},infrastructure={n:hashlib.sha256((b/n).read_bytes()).hexdigest() for n in ['S2W_run_host.py','S2W_lean_host.py']},workspace=str(b),cache=str(c))))
'''.replace('B',repr(B),1)
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 (E/f'NED_SETUP-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:
  lines=r.stdout.splitlines();(E/'NED_HOST_PINS.json').write_text(json.dumps(json.loads(lines[-1]),indent=1)+'\n');break
 if r.returncode not in (78,255):raise SystemExit(r.stderr+r.stdout)
 time.sleep(60 if r.returncode==255 else 180)
else:raise SystemExit('admission/transport exhausted')
print('setup admitted; cache and library pinned')
