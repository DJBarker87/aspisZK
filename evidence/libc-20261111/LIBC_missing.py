from pathlib import Path
import subprocess,json,re
E=Path(__file__).resolve().parent; src=E.parents[1]/'docs/research/100bit-spend-path-20261013/lean'
# All sources inspected only; exact unchanged bytes selected when a missing module is needed.
mods={p.stem:re.findall(r'^import ([\w.]+)',p.read_text(),re.M) for p in list(src.glob('*.lean'))+list((E/'LIBC_dependency_inputs').glob('*.lean'))}
code='''from pathlib import Path
import json
paths=PATHS;mods=MODS;seen=set();missing=[]
def visit(n):
 if n in seen:return
 seen.add(n)
 if any(Path(p,n.replace('.','/')+'.olean').is_file() for p in paths):return
 for d in mods.get(n,[]):visit(d)
 missing.append(dict(module=n,source_available=n in mods))
visit('RawTx1DigestLog');print(json.dumps(missing))
'''
paths=['/home/dombarker/project-offloads/codex-cx-libc-20261111/LIBC_objects']+json.loads((E/'LIBC_PATHS.json').read_text())
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input='PATHS='+repr(paths)+'\nMODS='+repr(mods)+'\n'+code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'LIBC_MISSING.json').write_text(r.stdout)
for x in json.loads(r.stdout):
 if x['source_available']:
  
  if (src/(x['module']+'.lean')).exists():(E/'LIBC_dependency_inputs'/ (x['module']+'.lean')).write_bytes((src/(x['module']+'.lean')).read_bytes())
print(r.stdout)
