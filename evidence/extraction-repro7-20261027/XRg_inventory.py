from pathlib import Path
import hashlib,json,sys
B=Path(__file__).resolve().parent;p=Path(sys.argv[1]);j=json.loads(p.read_text());table={}
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
def sha(x):return hashlib.sha256(json.dumps(x,sort_keys=True).encode()).hexdigest()
funs=j['translated']['fun_decls'];traits=j['translated']['trait_decls'];rows=[];missing=[]
def info(i):
 f=funs[i] if 0<=i<len(funs) else None
 if f is None:return dict(id=i,status='MISSING')
 meta=expand(f['item_meta']);name=meta['name']
 return dict(id=i,name=name,idents='::'.join(n['Ident'][0] for n in name if 'Ident' in n),status='declared opaque' if f['body']=='Opaque' else 'translated',span=meta['span'])
def walk(x):
 if isinstance(x,dict):
  if 'Call' in x and isinstance(x['Call'],dict) and 'call' in x['Call']:yield x['Call']['call']['func']
  for v in x.values():yield from walk(v)
 elif isinstance(x,list):
  for v in x:yield from walk(v)
for f in funs:
 if not f:continue
 row=info(f['def_id']);row['body_sha256']=sha(expand(f['body']));row['callees']=[]
 for c in walk(expand(f['body'])):
  if 'Dynamic' in c:r=dict(status='dynamic typed function parameter',operand=c['Dynamic'])
  else:
   kind=c['Regular']['kind']
   if 'Fun' in kind:
    k=kind['Fun'];r=info(k['Regular']) if 'Regular' in k else dict(status='translator builtin',builtin=k['Builtin'])
   elif 'Trait' in kind:
    tr,method=kind['Trait'];i=tr['trait_decl_ref']['skip_binder']['id'];td=expand(traits[i]) if traits[i] else None
    r=dict(status='declared trait parameter method' if td else 'MISSING',trait_id=i,method=method,trait_name=td['item_meta']['name'] if td else None,trait_reference=tr)
   else:r=dict(status='UNCLASSIFIED',kind=kind)
  if r['status'] in ['MISSING','UNCLASSIFIED']:missing.append(dict(caller=row['id'],callee=r))
  row['callees'].append(r)
 rows.append(row)
opaque=[r for r in rows if r['status']=='declared opaque' and r['idents'].startswith('aspis_r1_cost_probe')]
result=dict(artifact=str(p),sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),bytes=p.stat().st_size,has_errors=j['has_errors'],functions=rows,release_opaque=[{k:v for k,v in r.items() if k!='callees'} for r in opaque],missing_callees=missing,call_declaration_closed=not missing,typecheck_valid=j['has_errors'] is False,ready_for_aeneas=not missing and j['has_errors'] is False,qualification='Declaration closure only; library opaque/dynamic/trait calls remain explicit external semantics. Not source refinement or an association proof.')
out=B/(p.stem+'_inventory.json');out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['functions','release_opaque']}));print('opaque release leaves',len(opaque),'function entries',len(rows))
