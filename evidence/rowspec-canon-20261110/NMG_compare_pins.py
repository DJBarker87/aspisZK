from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
names=[('ledger24-20261110','NLX'),('tx1-observed-20261110','NLR'),('tx1-top-20261110','NLV'),('tx1-finish2-20261110','NLU'),('tx2-entry3-20261110','NLW'),('tx2-entry2-20261110','NLM')]
def suffix(p):return next(s for s in ['.olean.private','.olean.server','.olean','.ir'] if p.endswith(s))
index={};inputs=[]
for folder,pre in names:
 p=E.parent/folder/(pre+'_CLOSURE_PINS.json.xz')
 if not p.exists():continue
 raw=lzma.decompress(p.read_bytes());x=json.loads(raw);inputs.append(dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest()))
 rows=x['selected_objects'] if 'selected_objects' in x else list(x.values())
 assert all(isinstance(r,dict) and all(k in r for k in ['module','path','sha256','bytes']) for r in rows)
 for row in rows:
  index.setdefault((row['module'],suffix(row['path']),row['sha256']),dict(input=str(p),path=row['path']))
current=json.loads(lzma.decompress((E/'NMG_CLOSURE_PINS.json.xz').read_bytes()));matches=[];missing=[];own=[]
for row in current['selected_objects']:
 if '/NMG_objects/' in row['path']:own.append(row);continue
 key=(row['module'],suffix(row['path']),row['sha256'])
 if key in index:matches.append(dict(row,predecessor=index[key]))
 else:missing.append(row)
raw=json.dumps(dict(inputs=inputs,matched=matches,new_own_objects=own,unmatched=missing)).encode();p=E/'NMG_INHERITED_COMPARISON.json.xz';p.write_bytes(lzma.compress(raw,preset=1));p.with_suffix('.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(matched=len(matches),new_own=len(own),unmatched=len(missing))))
