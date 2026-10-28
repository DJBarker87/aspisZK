from NBF_host import *
# Only this job's rebuildable Rust target is removed. The designated persistent
# Lean cache, all source and every receipt are retained.
r=py(f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});target=b/'NBF_target'
objects=[str(p) for p in b.rglob('*.olean')]
assert not objects,objects
size=sum(p.stat().st_size for p in target.rglob('*') if p.is_file()) if target.exists() else 0
if target.exists():shutil.rmtree(target)
c=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027')
assert c.is_dir()
pins={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in c.rglob('*') if p.is_file()}}
print(json.dumps(dict(cache=pins,rust_target_bytes_removed=size,rust_target_absent=not target.exists(),private_lean_objects=objects,private_solver_files=[str(p) for p in (b/'NBF_tmp').rglob('*') if p.is_file()])))
''')
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);end=x.pop('cache');start=json.loads((E/'NBF_CACHE_START.json').read_text())
(E/'NBF_CACHE_END.json').write_text(json.dumps(end,indent=2,sort_keys=True)+'\n')
x['cache_start_files']=len(start);x['cache_end_files']=len(end)
x['initial_objects_missing']=[k for k in start if k not in end]
x['initial_objects_changed']=[k for k in start if k in end and end[k]!=start[k]]
x['cache_retained']=True
assert not x['initial_objects_missing'] and not x['initial_objects_changed'],x
(E/'NBF_CLEANUP.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(x))
