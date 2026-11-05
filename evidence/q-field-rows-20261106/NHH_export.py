from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
code='''from pathlib import Path
import json,hashlib,shutil,os
b=Path('/home/dombarker/project-offloads/codex-cx-q-field-rows-20261106');cache=Path('/home/dombarker/project-offloads/codex-cx-slice-d-field3-cache-20261104/NHH_exports_final_20261106');cache.mkdir(exist_ok=True)
old=cache.parent/'NHH_exports_20261106'
for n in ['objects','sources']:
 shutil.copytree(old/n,cache/n,dirs_exist_ok=True)
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  cwd=Path(os.readlink(p/'cwd'))
  if cwd==b or b in cwd.parents:active.append(dict(pid=p.name,cwd=str(cwd),command=(p/'cmdline').read_bytes().replace(b'\\0',b' ').decode(errors='replace')))
 except (FileNotFoundError,PermissionError,ProcessLookupError):pass
assert not active,active
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for sub,target in [('NHH_objects','objects'),('NHH_generated','sources')]:
 for p in (b/sub).rglob('*'):
  if p.is_file() and (sub=='NHH_generated'and p.suffix=='.lean'or sub=='NHH_objects'and any(str(p).endswith(s)for s in ['.olean','.olean.private','.olean.server','.ir'])):
   q=cache/target/p.relative_to(b/sub);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);assert sha(q)==sha(p);rows.append(dict(source=str(p),path=str(q),bytes=q.stat().st_size,sha256=sha(q)))
p=b/'NHH_native/NHH_Driver';q=cache/'native/NHH_Driver';q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q);assert sha(p)==sha(q);rows.append(dict(source=str(p),path=str(q),bytes=q.stat().st_size,sha256=sha(q)))
rows=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p))for p in cache.rglob('*')if p.is_file()]
config=json.loads((b/'NHH_L049.json').read_text());paths=[str(cache/'objects')]+[p for p in config['env']['LEAN_PATH'].split(':')if p!=str(b/'NHH_objects')]
for n in ['NHH_target','NHH_tmp','NHH_native','NHH_objects']:
 p=b/n
 if p.exists():shutil.rmtree(p)
print(json.dumps(dict(status='PASS',workspace_retained=str(b),exports=str(cache),cache_parent_retained='/home/dombarker/project-offloads/codex-cx-slice-d-field3-cache-20261104',files=rows,export_bytes=sum(x['bytes']for x in rows),recommended_LEAN_PATH=':'.join(paths),active_owned_processes=active,removed_only_own_rebuildable=['NHH_target','NHH_tmp','NHH_native','NHH_objects'],seed_cache_never_deleted=True)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
assert r.returncode==0,r.stderr;(E/'NHH_EXPORT.json').write_text(r.stdout);x=json.loads(r.stdout);print(json.dumps(dict(status=x['status'],files=len(x['files']),export_bytes=x['export_bytes'],active_owned_processes=x['active_owned_processes'])))
