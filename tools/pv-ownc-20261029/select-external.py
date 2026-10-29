"""Select the existing h4 external cohort privately; never rebuild a library."""
from pathlib import Path
import json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownc-20261029'
m=json.loads((R/'evidence/pv-world-20261028/external-object-manifest.json').read_text())
code='''from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-ownc-20261029/lean-objects')
rows=json.loads(MANIFEST);linked=[]
for r in rows:
 p=Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['object_sha256'],r['module']
 target=D/(r['module']+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
 for source,dest in [(p,target),(Path(str(p)+'.server'),Path(str(target)+'.server')),(Path(str(p)+'.private'),Path(str(target)+'.private')),(p.with_suffix('.ir'),target.with_suffix('.ir'))]:
  if source.exists():
   if dest.exists():assert hashlib.sha256(dest.read_bytes()).hexdigest()==hashlib.sha256(source.read_bytes()).hexdigest()
   else:dest.symlink_to(source);linked.append(str(dest))
print(json.dumps(dict(count=len(rows),links=len(linked),all_sha256_verified=True,reason='private namespace selection; absent Aeneas root in earlier directory; environment input repair; no external rebuild')))
'''.replace('MANIFEST',repr(json.dumps(m)))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'external-selection.json').write_text(r.stdout);print(r.stdout)
