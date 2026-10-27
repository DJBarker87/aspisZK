from pathlib import Path
import subprocess,json,shlex
E=Path(__file__).resolve().parent
script=r'''from pathlib import Path
import hashlib,json,shutil,os
B=Path('/home/dombarker/project-offloads/codex-cx-extraction-assoc6-20261027')
C=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
live=[]
for p in Path('/proc').glob('[0-9]*'):
 try:
  cwd=(p/'cwd').resolve();cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if (cwd==B or B in cwd.parents) and any(x in cmd for x in ['lean','cargo-kani','cbmc','S2W_']):live.append(dict(pid=p.name,command=cmd))
 except (OSError,RuntimeError):pass
assert not live,live
records=[]
for p in (B/'XRn_objects').rglob('*'):
 if p.is_file() and not p.is_symlink():records.append(dict(path=str(p.relative_to(B)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
lock=B/'XRn_crate/Cargo.lock'
lock_record=dict(sha256=hashlib.sha256(lock.read_bytes()).hexdigest(),bytes=lock.stat().st_size,text=lock.read_text()) if lock.exists() else None
rootpins={}
for n in ['FJu_Top.lean','FJu_Top.olean','S2W_lean_host.py','S2W_run_host.py']:
 p=C/n
 rootpins[str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
removed=[]
for n in ['XRn_objects','XRn_target','XRn_crate','.lake']:
 p=B/n
 if p.exists():
  assert not p.is_symlink()
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file() and not q.is_symlink())
  shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
print(json.dumps(dict(live_own_jobs=live,object_artifacts=records,removed=removed,retained_coherent_pins=rootpins,own_cargo_lock=lock_record,note='Only own rebuildable cache directories removed. Shared sources/objects, every key and all evidence retained. No unowned solver temp is removed.'),indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],capture_output=True,text=True,check=True)
x=json.loads(r.stdout);lock=x.pop('own_cargo_lock')
if lock:(E/'XRn_Cargo.lock.txt').write_text(lock.pop('text'));x['own_cargo_lock']=lock
(E/'XRn_CLEANUP.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(objects=len(x['object_artifacts']),removed_bytes=sum(r['bytes'] for r in x['removed']),live_own_jobs=x['live_own_jobs'])))
