"""Pin actual resolution, retain own cache, and remove only lane build scratch."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
pins=json.loads((E/'NDD_AUDIT_PINS.json').read_text());initial=json.loads((E/'NDD_SOURCE.json').read_text())
resolved=[l.strip() for l in (E/'NDD_L057/stdout.log').read_text().splitlines() if l.strip().endswith('.olean')]
code='''from pathlib import Path
import json,hashlib,shutil
x=json.loads(PAYLOAD);b=Path('/home/dombarker/project-offloads/codex-cx-native-front1-20261028');cache=b.parent/'codex-cx-front1-cache-20261028';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in x['pins']['selected_objects'].items():assert sha(Path(p))==h['sha256'],p
resolution={}
for n in x['resolved']:
 p=Path(n);resolution[n]=dict(sha256=sha(p),bytes=p.stat().st_size)
 if '/Aeneas' in n:assert x['initial']['library'][n]==sha(p),n
family={p:sha(Path(p)) for p in x['initial']['library']}
assert family==x['initial']['library']
tools={}
for n in ['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake']:
 p=Path(n);tools[n]=dict(sha256=sha(p),bytes=p.stat().st_size)
retained={};obj=b/'NDD_objects'
assert obj.is_dir() and not obj.is_symlink()
for p in obj.rglob('*'):
 if not p.is_file():continue
 n=p.relative_to(obj);assert n.parts[0].startswith('NDD_'),str(n)
 q=cache/n;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==sha(p),str(q)
 else:q.write_bytes(p.read_bytes())
 retained[str(p)]=dict(retained_path=str(q),sha256=sha(q),bytes=q.stat().st_size)
shutil.rmtree(obj);obj.symlink_to(cache,target_is_directory=True)
for p,h in x['pins']['selected_objects'].items():assert sha(Path(p))==h['sha256'],p
removed=[]
for name in ['NDD_target','NDD_ref_target']:
 p=b/name
 if p.exists():
  assert p.resolve().parent==b and not p.is_symlink(),str(p)
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
temps=[]
for p in (b/'NDD_tmp').rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem')):
  temps.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
print(json.dumps(dict(actual_resolved_objects=resolution,aeneas_library_family=family,lean_tools=tools,all_797_selected_pins_unchanged=True,retained_new_objects=retained,own_cache_retained=str(cache),compatible_object_symlink=str(obj),removed_build_targets=removed,removed_owned_solver_temps=temps,shared_tmp_untouched=True)))
'''.replace('PAYLOAD',repr(json.dumps(dict(pins=pins,initial=initial,resolved=resolved))))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NDD_POSTFLIGHT.log').write_text(r.stderr)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'NDD_POSTFLIGHT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(pins_unchanged=True,retained_objects=len(out['retained_new_objects']),removed_targets=len(out['removed_build_targets']),actual_aeneas_resolution=[p for p in out['actual_resolved_objects'] if '/Aeneas' in p])))
