"""Retain accepted own Lean objects, with source checks, in this job's cache.
No compilation, shared writes, wallet/key operations, or sibling cache changes.
"""
from pathlib import Path
import subprocess,json,hashlib
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026'
last={}
for p in sorted(ev.glob('*.json')):
 if p.stem.isdigit() and 41200 <= int(p.stem) <= 41499:
  r=json.loads(p.read_text())
  if r.get('exit')==0:last[r['module']]=r
items=[dict(module=m,source_sha256=r['source_sha256'],receipt=r['attempt']) for m,r in sorted(last.items())]
code='''from pathlib import Path
import hashlib,json,shutil
base=Path('/home/dombarker/project-offloads')
joint=base/'aspis-joint-20261019';own=base/'codex-pv-cb-20261026';out=[]
for row in ITEMS:
 m=row['module'];src=joint/'sources'/(m+'.lean');obj=joint/'objects'/(m+'.olean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==row['source_sha256'],m
 dest=own/'lean-objects'/(m+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 shutil.copy2(obj,dest)
 row.update(object_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),size=dest.stat().st_size,retained=str(dest));out.append(row)
print(json.dumps(dict(action='Retained checked Lean objects in own surviving cache; shared sources and objects unchanged',objects=out),indent=2))
'''.replace('ITEMS',repr(items))
s=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True)
(ev/'RESUME5-RETAINED-LEAN-CACHE.json').write_text(s+'\n');print('Retained',len(items),'objects')
