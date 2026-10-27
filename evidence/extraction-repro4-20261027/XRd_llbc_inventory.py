from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent
p=B/'XRd_release_candidate_tx1.llbc';j=json.loads(p.read_text())
table={}
def collect(x):
 if isinstance(x,dict):
  if list(x)==['HashConsedValue']:table[x['HashConsedValue'][0]]=x['HashConsedValue'][1]
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(j)
def expand(x):
 if isinstance(x,dict):
  if list(x)==['Deduplicated']:return expand(table[x['Deduplicated']])
  if list(x)==['HashConsedValue']:return expand(x['HashConsedValue'][1])
  return {k:expand(v) for k,v in x.items()}
 if isinstance(x,list):return [expand(v) for v in x]
 return x
rows=[]
for f in j['translated']['fun_decls']:
 if f:
  meta=expand(f['item_meta']);rows.append({'id':f['def_id'],'name':meta['name'],'body':'Opaque' if f['body']=='Opaque' else 'Present','body_sha256':hashlib.sha256(json.dumps(expand(f['body']),sort_keys=True).encode()).hexdigest()})
out={'input_sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),'functions':rows,'note':'read-only hash-cons expansion for inventory; translator consumes original LLBC unchanged'}
(B/'XRd_llbc_inventory.json').write_text(json.dumps(out,indent=2)+'\n')
for f in rows:
 if any(x in json.dumps(f['name']) for x in ['prepared_claim','for_range','checkpoint','Dot','tx1','query_loop','finish','check_values','expand_values','wide_view','echeck']):print(f['id'],f['body'],json.dumps(f['name']))
