"""Retain successful lane objects in OWN cache, then remove OWN rebuildable outputs."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
assert not (E/'NFV_ACTIVE.json').exists() and not (E/'NFV_B_LEAN_ACTIVE.json').exists()
mods=json.loads((E/'NFV_AUDIT_PLAN.json').read_text())['modules']+['NFV_Driver','NFV_Coherence']
code=f'''from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-pool-retdata3-20261104');cache=b.parent/'codex-cx-pool-retdata3-cache-20261104'
exports={{}};missing=[]
for n in {mods!r}:
 for suffix in ['.lean','.olean','.olean.private','.olean.server','.ir']:
  source=b/('NFV_B_generated' if suffix=='.lean' else 'NFV_B_objects')/(n+suffix)
  if not source.exists():
   if suffix in ['.lean','.olean']:missing.append(str(source))
   continue
  dest=cache/'NFV_final_objects_20261104'/source.name;dest.parent.mkdir(exist_ok=True)
  if dest.exists():assert dest.read_bytes()==source.read_bytes(),('never overwrite a differing export',str(dest))
  else:shutil.copy2(source,dest)
  exports[str(dest)]=dict(sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),bytes=dest.stat().st_size)
for name in ['NFV_Driver','NFV_Driver.c','NFV_Coherence','NFV_Coherence.c']:
 source=b/'NFO_native'/name
 if not source.exists():missing.append(str(source));continue
 dest=cache/'NFV_audit_native_20261104'/name;dest.parent.mkdir(exist_ok=True)
 if dest.exists():assert dest.read_bytes()==source.read_bytes()
 else:shutil.copy2(source,dest)
 exports[str(dest)]=dict(sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),bytes=dest.stat().st_size)
assert not missing,missing
# All validation scopes must have terminated before deleting these own build outputs.
terminal=[]
for p in b.glob('NFV_*[0-9][0-9][0-9]/receipt.json'):
 rc=json.loads(p.read_text());cg=Path(rc.get('cgroup',''))/'cgroup.procs'
 if cg.exists():assert not cg.read_text().strip(),('scope still populated',str(cg))
 terminal.append(rc['attempt'])
removed=[]
for name in ['NFV_target','NFV_extract_target','NFV_tmp','NFV_B_objects','NFV_C_objects','NFO_native']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
print(json.dumps(dict(exports=exports,removed_own_rebuildable=removed,cache_retained=True,terminal_receipts=len(terminal),disk_free_bytes=shutil.disk_usage(b).free),indent=1))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'NFV_EXPORTS.json').write_text(r.stdout);print(len(json.loads(r.stdout)['exports']),'retained cache artifacts')
