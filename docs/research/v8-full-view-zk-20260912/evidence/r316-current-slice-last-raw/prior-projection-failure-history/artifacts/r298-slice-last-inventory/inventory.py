"""Read-only typed dependency inventory for R294 Fun12, following pinned R274 rules."""
import hashlib, json, pathlib
ROOT=pathlib.Path(__file__).resolve().parent
SRC=ROOT.parent/'r294-private-norm-batch-extract/R294PrivateNormBatch.llbc'
PINNED=ROOT/'pinned-reorder_decls.rs'
EXPECTED_SRC='bf5ea0b6f68ab17ef73d3e721c70c9193a0682d95dcbcaf693e93187cf71da6f'
EXPECTED_PINNED='8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SRC)==EXPECTED_SRC and sha(PINNED)==EXPECTED_PINNED
raw=json.loads(SRC.read_text()); d=raw['translated']
assert raw['has_errors'] is False
GROUPS={'Type':'type_decls','Fun':'fun_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}
rows={(k,row['def_id']):row for k,tab in GROUPS.items() for row in d[tab] if isinstance(row,dict)}
labels={}
for ent in d.get('item_names',[]):
 key=ent.get('key',{})
 if len(key)==1:
  k,i=next(iter(key.items())); parts=[]
  for p in ent.get('value',[]):
   if isinstance(p,dict) and 'Ident' in p: parts.append(p['Ident'][0])
   elif isinstance(p,dict) and 'Impl' in p: parts.append('{Impl}')
   else: parts.append(str(p))
  labels[(k,i)]='::'.join(parts)
# Expand Charon's hash-consed wrappers as representation-only decoding.
cons={}
def collect(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in cons or cons[i]==v; cons[i]=v
  for v in x.values(): collect(v)
 elif isinstance(x,list):
  for v in x: collect(v)
collect(raw)
def decode(x,seen=()):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in seen; return decode(v,seen+(i,))
  if 'Deduplicated' in x:
   i=x['Deduplicated']; assert i in cons and i not in seen; return decode(cons[i],seen+(i,))
  return {k:decode(v,seen) for k,v in x.items()}
 if isinstance(x,list): return [decode(v,seen) for v in x]
 return x

def source_parent(row):
 src=decode(row.get('src'))
 if isinstance(src,dict) and 'TraitImpl' in src:
  i=src['TraitImpl'].get('impl_ref',{}).get('id'); return ('TraitImpl',i) if isinstance(i,int) else None
 if isinstance(src,dict) and 'TraitDecl' in src:
  i=src['TraitDecl'].get('trait_ref',{}).get('id'); return ('TraitDecl',i) if isinstance(i,int) else None
 return None
edges=set(); typed=[]; absent=[]; unknown=[]; defaults=[]
def edge(src,target,path):
 typed.append({'path':path,'target':list(target)})
 if target not in rows:
  absent.append({'from':list(src),'to':list(target),'path':path,'pinned_behavior':'get_item(target)==None; not inserted into dependency graph'})
  return
 edges.add((src,target))
def walk(x,src,path,suppressed):
 if isinstance(x,list):
  for i,v in enumerate(x): walk(v,src,f'{path}[{i}]',suppressed)
  return
 if not isinstance(x,dict): return
 if set(x)=={'Adt'}:
  a=x['Adt']
  if isinstance(a,dict) and set(a)=={'id','generics'}:
   walk(a['id'],src,path+'.Adt.id',suppressed); walk(a['generics'],src,path+'.Adt.generics',suppressed)
  elif isinstance(a,int): edge(src,('Type',a),path)
  elif isinstance(a,list):
   if path.endswith('.Aggregate[0]') and len(a)==3:
    walk(a[0],src,path+'.Adt[0]',suppressed)
   elif '.ptr_metadata.' in path and a==[None,[]]:
    pass
   elif '.Projection[' in path and '.Field[0]' in path and len(a)==2 and isinstance(a[0],int):
    pass
   else: unknown.append([path,'Adt-list',a])
  elif a!='Builtin': unknown.append([path,'Adt',a])
  return
 if 'Fun' in x:
  f=x['Fun']
  if isinstance(f,dict) and set(f)=={'Regular'} and isinstance(f['Regular'],int): edge(src,('Fun',f['Regular']),path+'.Fun.Regular')
  elif not (isinstance(f,dict) and set(f)=={'Builtin'}): unknown.append([path,'Fun',f])
 if 'Global' in x:
  g=x['Global']
  if isinstance(g,int): edge(src,('Global',g),path+'.Global')
  elif isinstance(g,dict) and isinstance(g.get('id'),int) and 'generics' in g:
   edge(src,('Global',g['id']),path+'.Global.id'); walk(g['generics'],src,path+'.Global.generics',suppressed)
  else: unknown.append([path,'Global',g])
 if 'trait_decl_ref' in x:
  tr=x['trait_decl_ref']; i=tr.get('skip_binder',{}).get('id') if isinstance(tr,dict) else None
  if isinstance(i,int):
   target=('TraitDecl',i); typed.append({'path':path+'.trait_decl_ref','target':list(target)})
   if target not in rows: absent.append({'from':list(src),'to':list(target),'path':path+'.trait_decl_ref','pinned_behavior':'get_item(target)==None; not inserted into dependency graph'})
   elif target!=suppressed: edges.add((src,target))
   walk(tr.get('regions',[]),src,path+'.trait_decl_ref.regions',suppressed); walk(tr.get('skip_binder',{}).get('generics',{}),src,path+'.trait_decl_ref.generics',suppressed)
  else: unknown.append([path,'trait_decl_ref',tr])
 if 'impl_ref' in x:
  ir=x['impl_ref']
  if isinstance(ir,dict) and isinstance(ir.get('id'),int):
   target=('TraitImpl',ir['id']); typed.append({'path':path+'.impl_ref','target':list(target)})
   if target not in rows: absent.append({'from':list(src),'to':list(target),'path':path+'.impl_ref','pinned_behavior':'get_item(target)==None; not inserted into dependency graph'})
   elif target!=suppressed: edges.add((src,target))
   walk(ir.get('generics',{}),src,path+'.impl_ref.generics',suppressed)
  else: unknown.append([path,'impl_ref',ir])
 if 'TraitImpl' in x:
  ir=x['TraitImpl']
  if isinstance(ir,dict) and isinstance(ir.get('id'),int):
   target=('TraitImpl',ir['id']); typed.append({'path':path+'.TraitImpl','target':list(target)})
   if target not in rows: absent.append({'from':list(src),'to':list(target),'path':path+'.TraitImpl','pinned_behavior':'get_item(target)==None; not inserted into dependency graph'})
   elif target!=suppressed: edges.add((src,target))
   walk(ir.get('generics',{}),src,path+'.TraitImpl.generics',suppressed)
  else: unknown.append([path,'TraitImpl',ir])
 if 'impl_trait' in x:
  it=x['impl_trait']
  if isinstance(it,dict) and isinstance(it.get('id'),int):
   target=('TraitDecl',it['id']); typed.append({'path':path+'.impl_trait','target':list(target)})
   if target not in rows: absent.append({'from':list(src),'to':list(target),'path':path+'.impl_trait','pinned_behavior':'get_item(target)==None; not inserted into dependency graph'})
   elif target!=suppressed: edges.add((src,target))
   walk(it.get('generics',{}),src,path+'.impl_trait.generics',suppressed)
  else: unknown.append([path,'impl_trait',it])
 if 'TraitMethod' in x:
  tm=x['TraitMethod']
  if isinstance(tm,list) and len(tm)==2 and all(isinstance(v,int) for v in tm):
   target=('TraitDecl',tm[0]); typed.append({'path':path+'.TraitMethod','target':list(target)})
   if target not in rows: absent.append({'from':list(src),'to':list(target),'path':path+'.TraitMethod','pinned_behavior':'get_item(target)==None; not inserted into dependency graph'})
   elif target!=suppressed: edges.add((src,target))
  else: unknown.append([path,'TraitMethod',tm])
 for k,v in x.items():
  if k in ('Adt','Fun','Global','trait_decl_ref','impl_ref','TraitImpl','impl_trait','TraitMethod'): continue
  if k=='id' and isinstance(v,int): continue
  walk(v,src,path+'.'+k,suppressed)

def payload(kind,row):
 v=decode(row)
 if kind=='Fun':
  srcv=v.get('src')
  if isinstance(srcv,dict) and 'TraitDecl' in srcv:
   i=srcv['TraitDecl'].get('trait_ref',{}).get('id')
   if isinstance(i,int):
    target=('TraitDecl',i); typed.append({'path':f'Fun[{row["def_id"]}].src.TraitDecl.trait_ref','target':list(target)})
    if target in rows: edges.add(((kind,row['def_id']),target))
    else: absent.append({'from':[kind,row['def_id']],'to':list(target),'path':'Fun TraitDecl source edge','pinned_behavior':'get_item(target)==None; not inserted into dependency graph'})
  return {k:v[k] for k in ('generics','signature','body')}
 if kind=='TraitDecl':
  out={k:v[k] for k in ('generics','implied_clauses','types','vtable')}
  for i,c in enumerate(v['consts']):
   out[f'const[{i}].ty']=c['ty']
   if c.get('default') is not None:
    g=c['default']; target=('Global',g['id']); defaults.append({'from':[kind,row['def_id']],'assoc_kind':'const','assoc_index':i,'to':list(target)}); edge((kind,row['def_id']),target,f'TraitDecl[{row["def_id"]}].const[{i}].default')
    out[f'const[{i}].default.generics']=g.get('generics',{})
  for i,m in enumerate(v['methods']):
   if m is None: continue
   out[f'method[{i}].params']=m['params']; out[f'method[{i}].signature']=m['skip_binder']['signature']
   if m['skip_binder'].get('default') is not None:
    f=m['skip_binder']['default']; target=('Fun',f['id']); defaults.append({'from':[kind,row['def_id']],'assoc_kind':'method','assoc_index':i,'to':list(target)}); edge((kind,row['def_id']),target,f'TraitDecl[{row["def_id"]}].method[{i}].default')
    out[f'method[{i}].default.generics']=f.get('generics',{})
  return out
 return {k:v for k,v in v.items() if k not in ('def_id','item_meta','src','is_global_initializer')}

root=('Fun',12)
assert root in rows
# Ensure the requested root's indexed item label is the std slice last method.
row=rows[root]; meta=decode(row['item_meta']); parts=[]
for p in meta['name']:
 if isinstance(p,dict) and 'Ident' in p: parts.append(p['Ident'][0])
 elif isinstance(p,dict) and 'Impl' in p: parts.append('<impl>')
label='::'.join(parts); assert parts[-1]=='last' and parts[:2]==['core','slice']
graph={}; visited=set(); active=[]
def visit(n):
 if n not in rows: return
 if n in active: return
 if n in visited: return
 active.append(n); src_row=rows[n]; refs_before=set(edges)
 walk(payload(n[0],src_row),n,f'{n[0]}[{n[1]}]',source_parent(src_row))
 graph[n]={b for a,b in edges if a==n}
 for dep in sorted(graph[n]): visit(dep)
 active.pop(); visited.add(n)
visit(root)
cycles=[]
# Re-run cycle detection over the completed directed graph.
state={}
def dfs(n,stack):
 state[n]=1
 for dep in graph.get(n,[]):
  if dep not in graph: continue
  if state.get(dep)==1: cycles.append([list(x) for x in stack+[dep]])
  elif state.get(dep)!=2: dfs(dep,stack+[dep])
 state[n]=2
for n in graph:
 if not state.get(n): dfs(n,[n])

# Locate exact root span/signature/body and persist decoded structures for review.
span=meta['span']['data']; file_id=span['file_id']; fileinfo=d['files'][file_id]
(ROOT/'fun12_signature.json').write_text(json.dumps(decode(row['signature']),indent=2)+'\n')
(ROOT/'fun12_body.json').write_text(json.dumps(decode(row['body']),indent=2)+'\n')
ordered_labels=[{'kind':k,'id':i,'name':labels.get((k,i),'(no item_names entry)'),'source_file':None,'span':None,'body_kind':None} for k,i in sorted(visited)]
for ent in ordered_labels:
 rr=rows[(ent['kind'],ent['id'])]; mm=decode(rr['item_meta']); sp=mm.get('span',{}).get('data',{})
 ent['source_file']=d['files'][sp.get('file_id',-1)].get('name') if isinstance(sp.get('file_id'),int) and sp['file_id']<len(d['files']) else None
 ent['span']={'file_id':sp.get('file_id'),'beg':sp.get('beg'),'end':sp.get('end')}
 ent['body_kind']='Structured' if isinstance(rr.get('body'),dict) and 'Structured' in rr['body'] else ('Opaque' if rr.get('body')=='Opaque' else 'no body')
report={
 'input_llbc_sha256':sha(SRC),'pinned_reorder_rules_sha256':sha(PINNED),
 'R294_extract_source_hashes':json.loads((ROOT.parent/'r294-private-norm-batch-extract/extract-command.json').read_text())['verified_source_hashes'],
 'R294_recorded_source_revision':json.loads((ROOT.parent/'r294-private-norm-batch-extract/extract-command.json').read_text())['source_revision_recorded'],
 'has_errors':raw['has_errors'],'root':{'kind':'Fun','id':12,'item_name':label,'signature':decode(row['signature']),'metadata':meta,'source_file':fileinfo,'body_kind':'Structured' if 'Structured' in row['body'] else 'non-structured','body_span':decode(row['body'])['Structured']['body']['span']['data'],'body_json':'fun12_body.json','body_json_sha256':sha(ROOT/'fun12_body.json'),'signature_json':'fun12_signature.json','signature_json_sha256':sha(ROOT/'fun12_signature.json')},
 'input_declaration_counts':{k:len(d[v]) for k,v in GROUPS.items()},
 'closure_counts':{k:sum(1 for a,_ in visited if a==k) for k in GROUPS},
 'reachable_declarations':ordered_labels,
 'dependency_edges':[{'from':list(a),'to':list(b)} for a,b in sorted(edges) if a in visited],
 'typed_references_seen':typed,'absent_references_filtered_by_pinned_get_item':absent,
 'reachable_trait_defaults':defaults,'cycles':cycles,'unknown_reference_shapes':unknown,
 'root_generic_counts':{'regions':len(decode(row['generics'])['regions']),'types':len(decode(row['generics'])['types']),'const_generics':len(decode(row['generics'])['const_generics']),'trait_clauses':len(decode(row['generics'])['trait_clauses'])},
 'ordered_decls_input_count':len(d['ordered_decls']),
 'closure_order_positions':{str(list(n)):next((ix for ix,it in enumerate(d['ordered_decls']) if len(it)==1 and next(iter(it.items()))[0]==n[0] and next(iter(next(iter(it.values())).items()))==('NonRec',n[1])),None) for n in visited},
 'closure_reaches_generic_iterator_try_fold':any(n[0]=='Fun' and 'try_fold' in labels.get(n,'') and 'Iterator' in labels.get(n,'') for n in visited),
 'core_slice_source_bytes_in_LLBC':fileinfo.get('contents') is not None,
 'core_slice_source_hash_note':'R294 LLBC maps file_id 14 to /rustc/library/core/src/slice/mod.rs with contents=null; no standalone file hash is exposed by this artifact. The R294 verified source-hash set covers project Rust inputs and Cargo files, listed separately.',
 'scope':'Read-only dependency inventory following pinned R274 Charon visitor logic; no translation, LLBC declaration edit, semantic projection, or theorem claim.'}
(ROOT/'inventory.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'root':label,'closure_counts':report['closure_counts'],'edge_count':len(report['dependency_edges']),'absent_refs':len(absent),'cycles':len(cycles),'unknown':len(unknown)},indent=2))

checksum_paths=[SRC,PINNED,ROOT.parent/'r294-private-norm-batch-extract/extract-command.json',ROOT.parent/'r294-private-norm-batch-extract/toolchain.txt',ROOT/'inventory.py',ROOT/'fun12_signature.json',ROOT/'fun12_body.json',ROOT/'inventory.json',ROOT/'README.md']
(ROOT/'checksums.sha256').write_text(''.join(f"{sha(p)}  {p.relative_to(ROOT.parent.parent)}\n" for p in checksum_paths))
