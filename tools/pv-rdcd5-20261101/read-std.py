"""Read-only capture of exact extant model sources for association design."""
from pathlib import Path
import subprocess,json,hashlib
H='dombarker@100.108.41.90';E=Path(__file__).resolve().parents[2]/'evidence/pv-rdcd5-20261101'
code='''from pathlib import Path
import json,hashlib
roots=[Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022/sources'),Path('/home/dombarker/project-offloads/aspis-joint-20261019/sources')]
rows=[]
for root in roots:
 for rel in ['Aeneas/Std/Slice.lean','Aeneas/Std/Array/ArraySlice.lean','Aeneas/Std/Array/Array.lean']:
  p=root/rel
  if p.exists():rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),text=p.read_text()))
print(json.dumps(rows))
'''
p=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);assert p.returncode==0,p.stderr
(E/'std-model-sources.json').write_text(p.stdout);print([(x['path'],len(x['text'])) for x in json.loads(p.stdout)])
