"""Prepare a declared-name universe and pin all tables read by the Lean scanner."""
from pathlib import Path
import hashlib,json,lzma
B=Path(__file__).resolve().parent
mods={};count=0
with (B/'NER_KNOWN.txt').open('w') as names, (B/'NER_MANIFEST.jsonl').open('w') as manifest:
 for line in (B/'NER_COHORT.jsonl').open():
  row=json.loads(line)
  for name in row.pop('names'):
   if '\n' in name:raise ValueError('newline in constant name')
   names.write(name+'\n');count+=1
  module=row['module'];assert module not in mods
  p=Path(row['path']);artifacts=[]
  for q in [p,Path(str(p)+'.server'),Path(str(p)+'.private')]:
   if q.exists():
    h=hashlib.sha256()
    with q.open('rb') as f:
     for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
    artifacts.append(dict(path=str(q),sha256=h.hexdigest(),bytes=q.stat().st_size))
  row['artifacts']=artifacts;mods[module]=row
  manifest.write(json.dumps(row,separators=(',',':'))+'\n')
for root in ['NDR_CombinedAudit','RPx_Deployed']:
 assert root in mods
for row in mods.values():
 assert all(n in mods for n in row['imports']),row['module']
print(json.dumps(dict(modules=len(mods),declarations=count)))
