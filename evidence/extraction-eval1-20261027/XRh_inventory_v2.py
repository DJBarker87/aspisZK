from pathlib import Path
import json,hashlib,sys
B=Path(__file__).resolve().parent
cases=['shared','distinct','context','borrow','arrow','full'];out={}
for case in cases:
 p=B/('XRh_'+case+'.llbc');v=json.loads(p.read_text());funs=v['translated']['fun_decls'];traits=v['translated']['trait_decls'];rows=[];missing=[];kinds={};calls=0
 trait_values={}
 def collect_traits(x):
  if isinstance(x,dict):
   if set(x)=={'Value'} and isinstance(x['Value'],list) and len(x['Value'])==2:
    i,payload=x['Value']
    if isinstance(payload,dict) and 'trait_decl_ref' in payload:
     assert i not in trait_values or trait_values[i]==payload,(case,i)
     trait_values[i]=payload
   for z in x.values():collect_traits(z)
  elif isinstance(x,list):
   for z in x:collect_traits(z)
 collect_traits(v)
 def trait_value(t):
  if 'Value' in t:return t['Value'][1]
  if 'Deduplicated' in t:return trait_values[t['Deduplicated']]
  return t
 def walk(x):
  if isinstance(x,dict):
   if 'Call' in x and isinstance(x['Call'],dict) and 'call' in x['Call']:yield x['Call']['call']['func']
   for z in x.values():yield from walk(z)
  elif isinstance(x,list):
   for z in x:yield from walk(z)
 for f in funs:
  if not f:continue
  meta=f['item_meta'];ids=[x['Ident'][0] for x in meta['name'] if 'Ident' in x];name='::'.join(ids)
  if ids and ids[0].startswith('aspis_'):rows.append(dict(id=f['def_id'],idents=name,name=meta['name'],started_from=meta.get('started_from'),body='opaque' if f['body']=='Opaque' else 'structured' if isinstance(f['body'],dict) and 'Structured' in f['body'] else str(f['body'])[:100],span=meta['span'],has_errors=meta.get('has_errors')))
  for c in walk(f['body']):
   calls+=1
   if 'Dynamic' in c:kind='Dynamic'
   elif 'Regular' in c:
    k=c['Regular']['kind'];kind=next(iter(k))
    if 'Fun' in k:
     i=k['Fun']
     if not isinstance(i,int) or not (0<=i<len(funs)) or funs[i] is None:missing.append(dict(caller=f['def_id'],callee=c))
    elif 'Trait' in k:
     tr,method=k['Trait'];tr=trait_value(tr);t=tr.get('trait_decl_ref',{});t=t.get('skip_binder',t);i=t.get('id')
     if not isinstance(i,int) or not (0<=i<len(traits)) or traits[i] is None:missing.append(dict(caller=f['def_id'],callee=c))
    elif kind not in ['Builtin']:missing.append(dict(caller=f['def_id'],callee=c))
   else:kind='Unclassified';missing.append(dict(caller=f['def_id'],callee=c))
   kinds[kind]=kinds.get(kind,0)+1
 r=dict(llbc=str(p),sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),bytes=p.stat().st_size,has_errors=v['has_errors'],function_entries=sum(f is not None for f in funs),call_sites=calls,call_kinds=kinds,missing_callees=missing,project_functions=rows,opaque_project_functions=[x for x in rows if x['body']=='opaque'],qualification='Direct LLBC call-site declaration inventory only; dynamic/trait calls and backend std externals retain their actual interpretation obligations. Not source refinement, Lean checking or release extraction.')
 (B/('XRh_'+case+'_inventory_v2.json')).write_text(json.dumps(r,indent=2)+'\n');out[case]={k:r[k] for k in ['sha256','bytes','has_errors','function_entries','call_sites','call_kinds']};out[case].update(missing_count=len(missing),project_opaque_count=len(r['opaque_project_functions']))
(B/'XRh_inventory_summary_v2.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
