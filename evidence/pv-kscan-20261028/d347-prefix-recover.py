from pathlib import Path
import json,hashlib
C=Path('/private/tmp/pv-kscan-cache-20261028');E=Path(__file__).resolve().parent;db=json.loads((C/'d347-source-db.json').read_text());host=json.loads((C/'d347-host-sources.json').read_text());ps=json.loads((E/'d347-input.json').read_text())['passes'];rs=json.loads((C/'d347-receipts.json').read_text());missing={}
for p in ps:
 r=rs[p['receipt_blob']]
 if not isinstance(r,dict):continue
 for k,v in r.get('inputs',{}).items():
  h=v.get('sha256')
  if h not in db and k.endswith(('.rs','Cargo.toml')):missing.setdefault(h,[]).append(k)
for h,paths in list(missing.items()):
 for p in paths:
  if p not in host:continue
  data=host[p]['text'];buf=''
  for line in data.splitlines(keepends=True):
   buf+=line
   for s in [buf,buf.rstrip()+'\n',buf.rstrip()+'\n\n']:
    if hashlib.sha256(s.encode()).hexdigest()==h:
     db[h]=dict(text=s,origin=p,kind='exact original receipt hash recovered as retained-file line prefix');print('RECOVERED',p,len(s));break
   if h in db:break
  if h in db:break
(C/'d347-source-db.json').write_text(json.dumps(db));print('remaining',[(h,paths) for h,paths in missing.items() if h not in db])
