"""Copy merged lane-C objects; retain hashes and never alter suppliers."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-lib-20261111'
paths=json.loads((E/'LIB_PATHS.json').read_text())
extra=[p for p in json.loads(Path('evidence/libc-20261111/LIBC_PATHS.json').read_text()) if p not in paths]
export='/home/dombarker/project-offloads/codex-cx-libc-20261111/LIBC_exports_final_20261111'
code='''from pathlib import Path
import json,shutil,hashlib
b=Path(%r); roots=%r; out=[]; destinations=[]
for i,root in enumerate(roots):
 src=Path(root); dst=b/('LIB_seedC'+str(i));dst.mkdir(exist_ok=True);destinations.append(str(dst))
 for p in src.rglob('*'):
  if p.is_file() and any(str(p).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):
   q=dst/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
   h=hashlib.sha256(p.read_bytes()).hexdigest()
   if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
   else:shutil.copy2(p,q)
   out.append(dict(source=str(p),destination=str(q),sha256=h))
print(json.dumps(dict(paths=destinations,files=out)))
'''%(B,[export]+extra)
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'LIB_C_IMPORTS.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'LIB_PATHS.json').write_text(json.dumps(x['paths']+paths,indent=2)+'\n')
print(len(x['files']))
