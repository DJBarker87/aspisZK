"""Admitted hash/export and own rebuildable-scratch cleanup. Never deletes the cache."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-d-entry2-20261106';H='dombarker@100.108.41.90'
pins=json.loads((E.parent/'slice-d-entry-20261105/NGL_TOOL_PINS.json').read_text())['pins']
code='''from pathlib import Path
import subprocess,json,sys,hashlib,shutil,time,os,resource
b=Path(B);p=b/'NHD_FINISH-reservation.json'
with (b/'NHD_FINISH-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
if not p.exists():print('MISSING');sys.exit(79)
a=json.loads(p.read_text());print(json.dumps(dict(exit=r.returncode,reservation=a)),flush=True)
if r.returncode or a.get('allowed') is not True:sys.exit(78)
start=time.monotonic();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tools=[]
for old in pins:
 path=Path(old['path'])
 if path.name=='S2W_run_host.py':path=b/path.name
 h=sha(path);assert h==old['sha256'],str(path);tools.append(dict(path=str(path),sha256=h,bytes=path.stat().st_size))
active=[]
for d in Path('/proc').iterdir():
 if d.name.isdigit():
  try:cmd=(d/'cmdline').read_bytes().replace(b'\\0',b' ').decode(errors='replace')
  except (FileNotFoundError,PermissionError,ProcessLookupError):continue
  if B in cmd and any(s in cmd for s in ['cargo-kani','kani-compiler','cbmc','cadical','S2W_run_host.py','bin/lean ']):active.append(dict(pid=d.name,command=cmd))
assert not active,active
assert sha(b/'NHD_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
cache=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104/NHD_exports_20261106');cache.mkdir(exist_ok=True)
exports=[]
for p in sorted((b/'NHD_objects').rglob('*')):
 if p.is_file():
  rel=p.relative_to(b/'NHD_objects');assert rel.parts[0].startswith('NHD_');q=cache/rel;q.parent.mkdir(parents=True,exist_ok=True);h=sha(p)
  if q.exists():assert sha(q)==h
  else:shutil.copy2(p,q)
  assert sha(q)==h;exports.append(dict(relative=str(rel),destination=str(q),sha256=h,bytes=p.stat().st_size))
removed=[]
for name in ['NHD_target','NHD_tmp','NHD_objects','NHD_native','__pycache__']:
 p=b/name
 if p.is_dir():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size,reason='own solver/build/object scratch; exported objects preserved'))
x=dict(status='PASS',cache_retained=str(cache),exports=exports,exported_bytes=sum(f['bytes'] for f in exports),removed_rebuildable_scratch=removed,active_owned_provers=active,tool_pins=tools,cache_never_deleted=True,no_wallet_or_key_action=True,source_revision=REV,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A: hash/file-copy/own-scratch cleanup only',disk=subprocess.check_output(['df','-h',str(b)],text=True))
(b/'NHD_EXPORTS.json').write_text(json.dumps(x,indent=1));print(json.dumps({k:v for k,v in x.items() if k not in ['exports','tool_pins']}))
'''
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\npins='+repr(pins)+'\nREV='+repr(rev)+'\n'+code,capture_output=True,text=True)
 (E/f'NHD_FINISH-transport-{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout[-1200:],flush=True)
 if r.returncode==0:break
 # Once export/cleanup starts, an uncertain transport needs read-only recovery.
 if r.returncode==255:raise RuntimeError('Recover finish state read-only; never resubmit cleanup after uncertain transport')
 if retry<10 and r.returncode in [78,79]:time.sleep(30 if r.returncode==79 else 180);continue
 raise SystemExit(r.returncode)
for n in ['NHD_EXPORTS.json','NHD_FINISH-reservation.json','NHD_FINISH-barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
