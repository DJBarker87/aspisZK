"""Read-only sibling import; copy missing Lean objects, pin source and bytes."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-lib-20261111'
S='/home/dombarker/project-offloads/codex-cx-libb-20261111'
paths=json.loads((E/'LIB_PATHS.json').read_text())
extra=[p for p in json.loads((E.parent/'libb-20261111/LIBB_PATHS.json').read_text()) if p not in paths]
pins={p.stem:hashlib.sha256(p.read_bytes()).hexdigest() for p in (E.parent/'libb-20261111').glob('LIBB_*.lean')}
code='''from pathlib import Path
import json,hashlib,shutil
b=Path(%r);s=Path(%r);dst=b/'LIB_seedB';dst.mkdir(exist_ok=True)
roots=%r;existing=%r;pins=%r;seen=set();rows=[];source_pins=[]
for root in existing:
 for p in Path(root).rglob('*.olean'):seen.add(str(p.relative_to(root)))
for root in roots:
 for p in sorted(Path(root).rglob('*.olean')):
  rel=p.relative_to(root)
  if str(rel) in seen:continue
  seen.add(str(rel))
  if p.stem.startswith('LIB_'):continue
  if root==str(s/'LIBB_objects') and p.stem in pins:
   src=s/'LIBB_generated'/p.with_suffix('.lean').name
   assert src.is_file(),src
   h=hashlib.sha256(src.read_bytes()).hexdigest();assert h==pins[p.stem],str(src)
   source_pins.append(dict(path=str(src),sha256=h))
  for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
   if not z.is_file():continue
   q=dst/z.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
   h=hashlib.sha256(z.read_bytes()).hexdigest()
   if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
   else:shutil.copy2(z,q)
   rows.append(dict(source=str(z),destination=str(q),sha256=h,bytes=z.stat().st_size))
print(json.dumps(dict(path=str(dst),objects=rows,sources=source_pins)))
'''%(B,S,[S+'/LIBB_objects']+extra,[B+'/LIB_objects']+paths,pins)
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'LIB_B_IMPORTS.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'LIB_PATHS.json').write_text(json.dumps([x['path']]+paths,indent=2)+'\n')
print(len(x['objects']),sum(z['bytes'] for z in x['objects']))
