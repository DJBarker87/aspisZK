"""Retain own copied imports/objects; never delete or mutate source caches."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code="""from pathlib import Path
import hashlib,shutil,json
B=Path('/home/dombarker/project-offloads/codex-pc-pool-ledger1-20261110');C=Path('/home/dombarker/project-offloads/codex-pc-pool-ledger1-cache-20261110');X=C/'PCE_exports_20261110';X.mkdir(exist_ok=True);rows=[]
for sub in ['PCE_objects','PCE_generated']:
 for p in (B/sub).rglob('*'):
  if p.is_file():
   rel=str(p.relative_to(B/sub));rel=('sources/'+rel) if sub=='PCE_generated' else rel;q=X/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
   h=hashlib.sha256(q.read_bytes()).hexdigest();assert h==hashlib.sha256(p.read_bytes()).hexdigest();rows.append(dict(path=str(q),source=str(p),sha256=h,bytes=q.stat().st_size))
q=X/'PCE_IMPORTS.json.xz';shutil.copyfile(B/q.name,q);rows.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
out=dict(export=str(X),base_cache=str(C),LEAN_PATH=[str(X),str(C)],files=rows,copy_only=True,cache_deleted=False,compiled_scratch_retained='Small own proof/audit objects retained for replay; no Rust target or solver scratch created',disk=shutil.disk_usage(B)._asdict())
(X/'PCE_EXPORT_MANIFEST.json').write_text(json.dumps(out,indent=1)+'\\n');print(json.dumps(out))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'PCE_EXPORT_MANIFEST.json').write_text(json.dumps(x,indent=1)+'\n');print('Retained own import cache and copied'+str(len(x['files']))+' own export files; no cache deletion or sibling write.')
