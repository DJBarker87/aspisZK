"""Compact exact caller/glue association. This is NOT an event refinement proof."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
p=D/'ProverRwFactoryCleanup.llbc';j=json.loads(p.read_text())['translated'];cons={}
def gather(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   k,v=x['HashConsedValue'];cons[k]=v
  for v in x.values():gather(v)
 elif isinstance(x,list):
  for v in x:gather(v)
def expand(x):
 if isinstance(x,dict):
  if 'Deduplicated' in x:return expand(cons[x['Deduplicated']])
  if 'HashConsedValue' in x:return expand(x['HashConsedValue'][1])
  return {k:expand(v) for k,v in x.items()}
 if isinstance(x,list):return [expand(v) for v in x]
 return x
def walk(x,path=''):
 if isinstance(x,dict):
  yield path,x
  for k,v in x.items():yield from walk(v,path+'/'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x):yield from walk(v,path+'/'+str(i))
gather(j);j=expand(j)
functions={f['def_id']:f for f in j['fun_decls'] if f}
rows=[]
for id,f in functions.items():
 name=f['item_meta']['name']; sig=f['signature'];body=f['body']
 if name[0].get('Ident',[''])[0] not in ['prover_rw_factory_cleanup','zeroize'] and id not in [143,159]:continue
 drops=[];calls=[]
 for path,x in walk(body):
  k=x.get('kind')
  if not isinstance(k,dict):continue
  if 'Drop' in k:
   d=k['Drop'];drops.append(dict(path=path,statement_id=x.get('id'),span=x.get('span'),place=d['place'],fn_ptr=d['fn_ptr'],kind=d['kind'],in_unwind='on_unwind' in path))
  if 'Call' in k:
   calls.append(dict(path=path,statement_id=x.get('id'),span=x.get('span'),call=k['Call']))
 locals=[]
 if isinstance(body,dict):locals=body['Structured']['locals']
 rows.append(dict(id=id,name=name,signature=sig,span=f['item_meta']['span'],body='opaque' if body=='Opaque' else 'structured',locals=locals,drops=drops,calls=calls))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out=dict(schema='ProverRwFactoryCleanup-source-glue-association-v1',input=dict(sha256=sha(p),size=p.stat().st_size),source_map_sha256=sha(D/'source-map.json'),functions=rows,claim='Fresh exact-item factory has precise caller Drop sites and unchanged zeroize source chain. Source association only; no accepted Aeneas translation or normal/unwind cleanup event theorem.',print_axioms='N/A: read-only source audit')
q=D/'source-audit.json';q.write_text(json.dumps(out,indent=2)+'\n');assert q.stat().st_size<=5_000_000
for r in rows:
 print(r['id'],str(r['name'])[-105:],r['body'],'drops',len(r['drops']),'normal',sum(not d['in_unwind'] for d in r['drops']))
