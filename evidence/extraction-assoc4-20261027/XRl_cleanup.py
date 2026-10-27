from pathlib import Path
import subprocess,json,shlex
E=Path(__file__).resolve().parent
script=r'''
from pathlib import Path
import hashlib,json,shutil,os
B=Path('/home/dombarker/project-offloads/codex-cx-extraction-assoc4-20261027')
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  cwd=(p/'cwd').resolve();args=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if cwd==B or B in cwd.parents:active.append(dict(pid=int(p.name),cwd=str(cwd),args=args))
 except (FileNotFoundError,PermissionError,ProcessLookupError):pass
if active:raise RuntimeError('Own active processes: '+json.dumps(active))
objects=[]
for p in sorted((B/'XRl_objects').rglob('*')):
 if p.is_file():objects.append(dict(path=str(p.relative_to(B)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
removed=[]
for name in ['XRl_target','XRl_objects','XRl_crate','.lake']:
 p=B/name
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file() and not q.is_symlink())
  removed.append(dict(path=str(p),bytes=size));shutil.rmtree(p)
x=dict(active_own_processes=active,removed=removed,object_manifest=objects,solver_temps='No solver temporary filename attributable to this run was emitted in K005 stdout; no unrelated /tmp file was removed.',retained='Own sources/receipts, coherent shared caches, other jobs and all keys retained; no wallet or account key created or cleaned up.')
(B/'XRl_cleanup.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],text=True,capture_output=True,check=True)
x=json.loads(r.stdout);(E/'XRl_cleanup.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({'removed_bytes':sum(p['bytes'] for p in x['removed']),'objects_pinned':len(x['object_manifest']),'active_own_processes':x['active_own_processes']}))
