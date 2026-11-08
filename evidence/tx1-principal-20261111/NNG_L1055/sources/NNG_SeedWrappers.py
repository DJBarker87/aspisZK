"""Copy immutable wrapper/dispatcher exports privately, retaining all pins."""
from pathlib import Path
import hashlib,json,shutil
B=Path.cwd();exports=json.loads((B/'NNG_WRAPPER_EXPORTS.json').read_text());dest=B/'NNG_Wrapper_objects';dest.mkdir(exist_ok=True)
selected={}
for entry in exports['NMV']['files']:
 p=Path(entry['path'])
 if p.name.startswith('NMV_') and any(p.name.endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):
  selected[p.name]=(p,entry['sha256'])
for entry in exports['NNF']['modules']:
 p=Path(entry['path']);selected[p.name]=(p,entry['sha256'])
 for suffix in ['.private','.server']:
  q=Path(str(p)+suffix)
  if q.is_file():selected[q.name]=(q,None)
 q=p.with_suffix('.ir')
 if q.is_file():selected[q.name]=(q,None)
# Resolve only the dispatcher predecessor modules from the pinned sibling env.
env=json.loads((B/'NNG_NNF_ENV.json').read_text());roots=env.get('LEAN_PATH',env.get('env',{}).get('LEAN_PATH','')).split(':')
for root in roots:
 p=Path(root)
 if not p.is_dir():continue
 for q in p.glob('NMW_*'):
  if q.is_file() and any(q.name.endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']) and q.name not in selected:
   selected[q.name]=(q,None)
rows=[]
for name,(source,expected) in sorted(selected.items()):
 data=source.read_bytes();sha=hashlib.sha256(data).hexdigest()
 if expected:assert sha==expected,(source,expected,sha)
 target=dest/name
 if target.exists():assert hashlib.sha256(target.read_bytes()).hexdigest()==sha,target
 else:shutil.copy2(source,target)
 rows.append(dict(source=str(source),path=str(target),sha256=sha,bytes=len(data),export_verified=expected is not None))
(B/'NNG_WRAPPER_SEED_PINS.json').write_text(json.dumps(rows,indent=2))
print(json.dumps({'files':len(rows),'bytes':sum(r['bytes'] for r in rows),'destination':str(dest)}))
