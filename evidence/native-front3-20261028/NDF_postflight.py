from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front3-20261028'
x=dict(B=B,pins=json.loads((E/'NDF_AUDIT_PINS.json').read_text()))
code='''from pathlib import Path
import json,hashlib,subprocess,shutil
x=json.loads(PAYLOAD);b=Path(x['B']);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]
for v in x['pins']['selected_objects'].values():
 p=Path(v['path'])
 if not p.is_file() or sha(p)!=v['sha256']:errors.append(str(p))
assert not errors,errors
ps=subprocess.check_output(['ps','-eo','pid,ppid,args'],text=True)
active=[l for l in ps.splitlines() if str(b) in l]
assert not active,active
cache=b.parent/'codex-cx-front3-cache-20261028';dest=cache/'NDF_objects'
objects={str(p.relative_to(b/'NDF_objects')):dict(sha256=sha(p),bytes=p.stat().st_size) for p in (b/'NDF_objects').rglob('*.olean')}
if (b/'NDF_objects').is_symlink():
 assert (b/'NDF_objects').resolve()==dest.resolve()
else:
 assert not dest.exists();shutil.move(str(b/'NDF_objects'),str(dest));(b/'NDF_objects').symlink_to(dest,target_is_directory=True)
removed={}
for n in ['NDF_target','NDF_ref_target','NDF_tmp']:
 p=b/n
 if p.exists():
  removed[n]=sum(q.stat().st_size for q in p.rglob('*') if q.is_file())
  shutil.rmtree(p)
print(json.dumps(dict(selected_objects_checked=len(x['pins']['selected_objects']),pin_errors=errors,active_processes=active,retained_cache=str(cache),retained_objects=objects,removed_rebuildable_bytes=removed,shared_tmp_touched=False,cache_deleted=False,free_bytes=shutil.disk_usage(b).free)))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NDF_POSTFLIGHT.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stderr+r.stdout
(E/'NDF_POSTFLIGHT.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print(json.dumps({k:v for k,v in json.loads(r.stdout).items() if k!='retained_objects'}))
