"""Inventory and remove only this job's disposable build outputs, no keys."""
from pathlib import Path
import json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
code='''from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-fxmem-20261028')
known=['drop-u32-03/check','zeroize-04/check','zeroize-04/libzeroize.rlib','reserve-05/check','zeroize-drop-06/check']
rows=[]
for name in known:
 p=D/name
 if not p.exists():rows.append(dict(path=str(p),already_absent=True));continue
 assert p.is_file() and not p.is_symlink(),p
 rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,kind='own disposable native output'))
objects=D/'lean-objects'
assert objects.is_dir() and not objects.is_symlink()
for p in sorted(objects.rglob('*')):
 if p.is_symlink():rows.append(dict(path=str(p),kind='own dependency symlink',target=str(p.resolve())))
 elif p.is_file():
  assert '.olean' in p.name or p.suffix=='.ilean',p
  rows.append(dict(path=str(p),kind='own private Lean output',sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
# Write inventory before removal. Symlink targets in shared caches are never
# followed or removed; rmtree removes only this job's private directory.
j=dict(outputs=rows,shared_cache_removed=False,source_or_evidence_removed=False,keys_created_or_cleaned=False)
(D/'cleanup-resume.json').write_text(json.dumps(j,indent=2)+'\\n')
for name in known:
 p=D/name
 if p.exists():p.unlink()
shutil.rmtree(objects)
j['removed']=True;j['private_objects_absent']=not objects.exists()
(D/'cleanup-resume.json').write_text(json.dumps(j,indent=2)+'\\n')
print(json.dumps(j))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
j=json.loads(r.stdout);(E/'cleanup-resume.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(dict(removed=j['removed'],outputs=len(j['outputs']),private_objects_absent=j['private_objects_absent'],shared_cache_removed=False,keys_created_or_cleaned=False)))
