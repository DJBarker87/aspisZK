"""Copy missing flat modules from the supplier's exact ordered LEAN_PATH.
No recursive cache traversal; nested namespaces remain supplied by retained cache.
"""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
paths=json.load(open('evidence/tx1-principal-20261111/NNG_L362/receipt.json'))['env']['LEAN_PATH'].split(':')
code='''from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-integrate-20261111');own=[b/'NNH_objects',b/'NNH_seed',b/'NNH_library_seed'];out=[]
assert shutil.disk_usage(b).free>=40_000_000_000
for root in paths:
 for src in sorted(Path(root).glob('*.olean')):
  if any((p/src.name).is_file() for p in own):continue
  for p in [src,Path(str(src)+'.private'),Path(str(src)+'.server'),src.with_suffix('.ir')]:
   if not p.is_file():continue
   q=own[1]/p.name;shutil.copy2(p,q);out.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='paths='+repr(paths)+'\n'+code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'NNH_FINISH_DEPENDENCY_IMPORTS.json').write_text(r.stdout);print('copied',len(json.loads(r.stdout)))
