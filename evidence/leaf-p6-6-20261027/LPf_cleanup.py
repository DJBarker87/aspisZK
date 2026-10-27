"""Audit shared objects and remove only this job's rebuildable private caches."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-leaf-p6-6-20261027';deps={}
for p in E.glob('LPf_L*/receipt.json'):
 r=json.loads(p.read_text())
 for x in r.get('deps_fingerprint',{}).get('selected_objects',{}).values():
  if not x['path'].startswith(B+'/'):deps[x['path']]=x['sha256']
code='''from pathlib import Path
import json,hashlib,os,shutil
B=Path(%r);expected=%r
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdecimal():continue
 try:
  cmd=(p/'cmdline').read_bytes().replace(b'\\0',b' ').decode(errors='replace')
  cwd=(p/'cwd').resolve()
 except (OSError,RuntimeError):continue
 if (str(cwd).startswith(str(B)) or 'LPf_' in cmd) and any(t in cmd for t in ['cargo-kani','kani-compiler','cbmc ','rustc ','lake env lean','/bin/lean ']):active.append({'pid':p.name,'command':cmd,'cwd':str(cwd)})
assert not active,active
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
before={p:sha(p) for p in expected};assert before==expected,'shared object drift before cleanup'
objects={str(p.relative_to(B)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in (B/'LPf_objects').rglob('*') if p.is_file()}
removed={};tmp=[str(p.relative_to(B)) for p in (B/'LPf_tmp').rglob('*') if p.is_file()]
for name in ['LPf_target','LPf_objects','LPf_tmp']:
 p=B/name;assert p.resolve().parent==B.resolve()
 if p.exists():
  removed[name]=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p)
after={p:sha(p) for p in expected};assert before==after,'shared object changed during cleanup'
lock=sha(B/'LPf_src/Cargo.lock')
out={'active_builds':active,'removed_logical_bytes':removed,'private_object_hashes':objects,'own_solver_temporary_files':tmp,'shared_object_hashes':after,'shared_objects_unchanged':True,'scratch_lock_after_stop_sha256':lock,'scope':'Only own compiled caches removed. Sources, receipts, shared caches and keys untouched.'}
(B/'LPf_cleanup.json').write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps(out))
'''%(B,deps)
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True)
(E/'LPf_cleanup.log').write_text(r.stderr)
if r.returncode:raise SystemExit(r.stderr)
out=json.loads(r.stdout);(E/'LPf_cleanup.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'removed_logical_bytes':out['removed_logical_bytes'],'shared_objects':len(out['shared_object_hashes']),'shared_objects_unchanged':out['shared_objects_unchanged'],'active_builds':out['active_builds']}))
