"""Read/hash pins, retain own objects, clean only rebuildable job scratch."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
x=dict(pins=json.loads((E/'NDL_AUDIT_PINS.json').read_text()),initial=json.loads((E/'NDL_SOURCE.json').read_text()))
code=r'''from pathlib import Path
import json,hashlib,shutil
x=json.loads(PAYLOAD);b=Path('/home/dombarker/project-offloads/codex-cx-native-front1b-20261028');cache=b.parent/'codex-cx-front1-cache-20261028';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in x['pins']['selected_objects'].items():assert sha(Path(n))==h['sha256'],n
family={n:sha(Path(n)) for n in x['initial']['library']};assert family==x['initial']['library']
tools={}
for n in ['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon','/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended']:
 p=Path(n);tools[n]=dict(sha256=sha(p),bytes=p.stat().st_size)
retained={};obj=b/'NDL_objects';assert obj.is_dir() and not obj.is_symlink()
for p in obj.rglob('*.olean'):
 n=p.relative_to(obj);q=cache/n;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==sha(p),str(q)
 else:q.write_bytes(p.read_bytes())
 retained[str(p)]=dict(retained_path=str(q),sha256=sha(q),bytes=q.stat().st_size)
removed=[]
# Receipt/source snapshots survive; own cache is NEVER deleted.
for name in ['NDL_target','NDL_ref_target']:
 p=b/name
 if p.exists():
  assert p.resolve().parent==b and not p.is_symlink(),str(p)
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
temps=[]
for p in (b/'NDL_tmp').rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem')):
  temps.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
# Keep the compatible objects path, but remove its redundant scratch copy.
shutil.rmtree(obj);obj.symlink_to(cache,target_is_directory=True)
for n,h in x['pins']['selected_objects'].items():assert sha(Path(n))==h['sha256'],n
print(json.dumps(dict(aeneas_library_family=family,tool_pins=tools,selected_pins_unchanged=True,retained_objects=retained,own_cache_retained=str(cache),compatible_object_symlink=str(obj),removed_build_targets=removed,removed_owned_solver_temps=temps,shared_tmp_untouched=True)))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NDL_POSTFLIGHT.log').write_text(r.stderr);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'NDL_POSTFLIGHT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(pins_unchanged=True,retained_objects=len(out['retained_objects']),removed_targets=len(out['removed_build_targets']))))
