#!/usr/bin/env python3
"""Metadata-only typed/transitive projection of three unchanged R327 LLBC roots."""
import copy, hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SRC=ROOT.parent/'r327-private-batch-source-try-fold/R327PrivateBatchSourceTryFold.llbc'
EXPECTED='9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442'
GROUPS={'Type':'type_decls','Fun':'fun_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}
ROOTS=[('Fun',37),('Fun',39),('Fun',40)]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SRC)==EXPECTED
raw=json.loads(SRC.read_text()); d=raw['translated']
assert raw['has_errors'] is False
rows={(kind,row['def_id']):(ix,row) for kind,key in GROUPS.items() for ix,row in enumerate(d[key]) if isinstance(row,dict)}
assert all(r in rows for r in ROOTS)
# Match exact identities in R327 source-body audit before closure traversal.
source_audit=ROOT.parent/'r327-private-batch-source-try-fold/source-body-audit'
audit=json.loads((source_audit/'body-audit.json').read_text())
targets={x['id']:x['name'] for x in audit['target_methods']}
expected_names={37:'core::ops::control_flow::{impl-trait#20}::branch',39:'core::ops::control_flow::{impl-trait#20}::from_output',40:'core::ops::control_flow::{impl-trait#23}::from_residual'}
assert all(targets.get(i)==nm for i,nm in expected_names.items()),targets
assert audit['evidence']['R327_llbc_sha256']==EXPECTED

# Charon hash-cons table: validate original ID/value uniqueness and resolve wrappers.
hc={}
def collect(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in hc or hc[i]==v; hc[i]=v
  for v in x.values(): collect(v)
 elif isinstance(x,list):
  for v in x: collect(v)
collect(raw)
def decode(x,seen=()):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in seen; return decode(v,seen+(i,))
  if 'Deduplicated' in x:
   i=x['Deduplicated']; assert i in hc and i not in seen; return decode(hc[i],seen+(i,))
  return {k:decode(v,seen) for k,v in x.items()}
 if isinstance(x,list): return [decode(v,seen) for v in x]
 return x

# Typed ID references recognized using the serialized LLBC constructor forms.
refs=[]; unknown_ref_shapes=[]; edges={n:set() for n in ROOTS}; missing=[]
def add(src,target,path,ref_kind):
 refs.append({'from':list(src),'to':list(target),'path':path,'ref_kind':ref_kind})
 if target not in rows: missing.append({'from':list(src),'to':list(target),'path':path,'ref_kind':ref_kind})
 else: edges.setdefault(src,set()).add(target)
def walk(x,src,path):
 if isinstance(x,list):
  for i,v in enumerate(x): walk(v,src,f'{path}[{i}]')
  return
 if not isinstance(x,dict): return
 # ADT declaration ID; builtin tuple/array/vector forms are not declaration rows.
 if set(x)=={'Adt'}:
  val=x['Adt']
  if isinstance(val,int): add(src,('Type',val),path,'Adt')
  elif isinstance(val,list) and len(val)>=2 and isinstance(val[0],int) and isinstance(val[1],int): add(src,('Type',val[0]),path+'.Adt[0]','AdtVariant')
  elif isinstance(val,list) and len(val)>=2 and isinstance(val[0],dict) and isinstance(val[0].get('id'),dict) and isinstance(val[0]['id'].get('Adt'),int):
   add(src,('Type',val[0]['id']['Adt']),path+'.Adt[0].id.Adt','AdtVariant'); walk(val[0].get('generics',{}),src,path+'.Adt[0].generics')
  elif isinstance(val,dict) and isinstance(val.get('id'),dict) and isinstance(val['id'].get('Adt'),int):
   add(src,('Type',val['id']['Adt']),path+'.Adt.id.Adt','Adt'); walk(val.get('generics',{}),src,path+'.Adt.generics')
  elif isinstance(val,dict) and isinstance(val.get('id'),str) and 'generics' in val:
   walk(val.get('generics',{}),src,path+'.Adt.generics')
  elif val not in ('Builtin','Tuple','Array','Slice','Never','Str','RawPtr','Ref','FnPtr'):
   unknown_ref_shapes.append({'path':path,'shape':'Adt','value':val})
  return
 # Field projection IDs are [ADT type id, field index]; the second integer is not a row ref.
 if set(x)=={'Field'} and isinstance(x['Field'],list) and len(x['Field'])==2 and all(isinstance(v,int) for v in x['Field']):
  add(src,('Type',x['Field'][0]),path+'.Field[0]','AdtFieldOwner'); return
 # Aggregate IDs carry an ADT type ID and variant index.
 if set(x)=={'Aggregate'} and isinstance(x['Aggregate'],dict) and isinstance(x['Aggregate'].get('Adt'),list) and len(x['Aggregate']['Adt'])>=2:
  aggregate=x['Aggregate']['Adt']; aid=aggregate[0]
  if isinstance(aid,dict) and isinstance(aid.get('id'),dict) and isinstance(aid['id'].get('Adt'),int):
   add(src,('Type',aid['id']['Adt']),path+'.Aggregate[0].id.Adt','AdtAggregate')
   walk(aid.get('generics',{}),src,path+'.Aggregate[0].generics')
  else: unknown_ref_shapes.append({'path':path,'shape':'AggregateAdtId','value':aid})
  for i,v in enumerate(aggregate[2:],2): walk(v,src,f'{path}.Aggregate.Adt[{i}]')
  return
 if 'Adt' in x and isinstance(x['Adt'],dict) and set(x['Adt'])=={'id','generics'}:
  walk(x['Adt']['id'],src,path+'.Adt.id'); walk(x['Adt']['generics'],src,path+'.Adt.generics')
 if 'Fun' in x:
  f=x['Fun']
  if isinstance(f,dict) and set(f)=={'Regular'} and isinstance(f['Regular'],int): add(src,('Fun',f['Regular']),path+'.Fun.Regular','Fun')
  elif isinstance(f,dict) and set(f)=={'Builtin'}: pass
  else: unknown_ref_shapes.append({'path':path,'shape':'Fun','value':f})
 if 'Global' in x:
  g=x['Global']
  if isinstance(g,int): add(src,('Global',g),path+'.Global','Global')
  elif isinstance(g,dict) and isinstance(g.get('id'),int) and 'generics' in g:
   add(src,('Global',g['id']),path+'.Global.id','Global'); walk(g['generics'],src,path+'.Global.generics')
  else: unknown_ref_shapes.append({'path':path,'shape':'Global','value':g})
 if 'trait_decl_ref' in x:
  tr=x['trait_decl_ref']; i=tr.get('skip_binder',{}).get('id') if isinstance(tr,dict) else None
  if isinstance(i,int): add(src,('TraitDecl',i),path+'.trait_decl_ref','TraitDecl'); walk(tr.get('regions',[]),src,path+'.trait_decl_ref.regions'); walk(tr['skip_binder'].get('generics',{}),src,path+'.trait_decl_ref.generics')
  else: unknown_ref_shapes.append({'path':path,'shape':'trait_decl_ref','value':tr})
 if 'impl_ref' in x:
  ir=x['impl_ref']
  if isinstance(ir,dict) and isinstance(ir.get('id'),int): add(src,('TraitImpl',ir['id']),path+'.impl_ref','TraitImpl'); walk(ir.get('generics',{}),src,path+'.impl_ref.generics')
  else: unknown_ref_shapes.append({'path':path,'shape':'impl_ref','value':ir})
 if 'TraitImpl' in x:
  tr=x['TraitImpl']
  if isinstance(tr,dict) and isinstance(tr.get('id'),int): add(src,('TraitImpl',tr['id']),path+'.TraitImpl','TraitImpl'); walk(tr.get('generics',{}),src,path+'.TraitImpl.generics')
  elif isinstance(tr,dict) and isinstance(tr.get('impl_ref'),dict) and isinstance(tr['impl_ref'].get('id'),int):
   add(src,('TraitImpl',tr['impl_ref']['id']),path+'.TraitImpl.impl_ref','TraitImplSource')
   walk(tr['impl_ref'].get('generics',{}),src,path+'.TraitImpl.impl_ref.generics')
   tref=tr.get('trait_ref',{})
   if isinstance(tref,dict) and isinstance(tref.get('id'),int): add(src,('TraitDecl',tref['id']),path+'.TraitImpl.trait_ref','TraitDeclSource'); walk(tref.get('generics',{}),src,path+'.TraitImpl.trait_ref.generics')
   else: unknown_ref_shapes.append({'path':path+'.TraitImpl.trait_ref','shape':'TraitDeclSource','value':tref})
  else: unknown_ref_shapes.append({'path':path,'shape':'TraitImpl','value':tr})
 if 'impl_trait' in x:
  it=x['impl_trait']
  if isinstance(it,dict) and isinstance(it.get('id'),int): add(src,('TraitDecl',it['id']),path+'.impl_trait','TraitDecl'); walk(it.get('generics',{}),src,path+'.impl_trait.generics')
  else: unknown_ref_shapes.append({'path':path,'shape':'impl_trait','value':it})
 if 'TraitMethod' in x:
  tm=x['TraitMethod']
  if isinstance(tm,list) and len(tm)==2 and all(isinstance(v,int) for v in tm): add(src,('TraitDecl',tm[0]),path+'.TraitMethod','TraitDecl')
  else: unknown_ref_shapes.append({'path':path,'shape':'TraitMethod','value':tm})
 # Avoid double traversal of typed reference payloads and arbitrary integer IDs.
 skip={'Adt','Fun','Global','trait_decl_ref','impl_ref','TraitImpl','impl_trait','TraitMethod'}
 for k,v in x.items():
  if k in skip or (k=='id' and isinstance(v,int)): continue
  walk(v,src,path+'.'+k)

# Include all declaration row content except item metadata (names/spans are labels,
# not typed AST edges); explicitly include source origins and table-typed source refs.
reachable=set(); todo=list(ROOTS)
while todo:
 node=todo.pop()
 if node in reachable: continue
 if node not in rows: missing.append({'to':list(node),'path':'closure queue','ref_kind':'missing declaration'}); continue
 reachable.add(node); edges.setdefault(node,set())
 row=rows[node][1]
 payload={k:v for k,v in row.items() if k not in ('def_id','item_meta')}
 walk(decode(payload),node,f'{node[0]}[{node[1]}]')
 for dest in sorted(edges[node]):
  if dest not in reachable: todo.append(dest)

# No source row is fabricated. Stop if typed refs remain unknown or point to absent rows.
assert not missing, missing
assert not unknown_ref_shapes, unknown_ref_shapes
all_order=[]; seen_order=set()
for entry in d['ordered_decls']:
 for kind,payload in entry.items():
  if isinstance(payload,dict) and 'NonRec' in payload and isinstance(payload['NonRec'],int):
   node=(kind,payload['NonRec'])
   if node in reachable:
    assert node not in seen_order
    seen_order.add(node); all_order.append(node)
assert seen_order <= reachable
# Every present reachable declaration must have its original order entry; no synthetic ordering.
ordered_missing=sorted(reachable-seen_order)

out=copy.deepcopy(raw); od=out['translated']
for kind,key in GROUPS.items():
 od[key]=[row if isinstance(row,dict) and (kind,row.get('def_id')) in reachable else None for row in d[key]]
def typed_key(row,table):
 if not isinstance(row,dict) or not isinstance(row.get('key'),dict) or len(row['key'])!=1: raise ValueError(('unknown typed-name row',table,row))
 kind,i=next(iter(row['key'].items()))
 if kind not in GROUPS or not isinstance(i,int): raise ValueError(('unknown typed-name key',table,row.get('key')))
 return kind,i
for table in ('item_names','short_names'):
 od[table]=[row for row in d[table] if typed_key(row,table) in reachable]
# assoc_item_names is parallel trait-declaration metadata, not declaration rows;
# preserve it byte/decoded-value-identically as R309 did.
keep_order=[]
for entry in d['ordered_decls']:
 if len(entry)!=1: raise ValueError(('unexpected multi-declaration ordered entry',entry))
 kind,payload=next(iter(entry.items()))
 if not isinstance(payload,dict) or set(payload)!={'NonRec'}: raise ValueError(('unexpected ordered_decls shape',entry))
 if (kind,payload['NonRec']) in reachable: keep_order.append(entry)
od['ordered_decls']=keep_order

# Re-emit only original hash-cons values referenced by the projected object,
# preserving each ID and value and replacing subsequent first-seen references by Deduplicated.
emitted=set()
def rehash(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i=x['HashConsedValue'][0]; assert i in hc
   if i in emitted:return {'Deduplicated':i}
   emitted.add(i); return {'HashConsedValue':[i,rehash(hc[i])]}
  if 'Deduplicated' in x:
   i=x['Deduplicated']; assert i in hc
   if i in emitted:return {'Deduplicated':i}
   emitted.add(i); return {'HashConsedValue':[i,rehash(hc[i])]}
  return {k:rehash(v) for k,v in x.items()}
 if isinstance(x,list):return [rehash(v) for v in x]
 return x
OUT=ROOT/'R334ControlFlowSourceProjection.llbc'; OUT.write_text(json.dumps(rehash(out),indent=2)+'\n')
# Read-back completeness and exact row equality after hash-cons resolution.
outraw=json.loads(OUT.read_text()); out_hc={}
def collect_out(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in out_hc or out_hc[i]==v;out_hc[i]=v
  for v in x.values():collect_out(v)
 elif isinstance(x,list):
  for v in x:collect_out(v)
collect_out(outraw)
# independent generic decode accepts an explicit table

def dec(x,table,seen=()):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue'];assert i not in seen;return dec(v,table,seen+(i,))
  if 'Deduplicated' in x:
   i=x['Deduplicated'];assert i in table and i not in seen;return dec(table[i],table,seen+(i,))
  return {k:dec(v,table,seen) for k,v in x.items()}
 if isinstance(x,list):return [dec(v,table,seen) for v in x]
 return x
for kind,key in GROUPS.items():
 assert len(outraw['translated'][key])==len(d[key])
 for ix,(before,after) in enumerate(zip(d[key],outraw['translated'][key])):
  retain=isinstance(before,dict) and (kind,before.get('def_id')) in reachable
  assert (after is not None)==retain,(kind,ix,retain,after is None)
for node in reachable:
 ix,srcrow=rows[node]; outrow=outraw['translated'][GROUPS[node[0]]][ix]
 assert outrow is not None and outrow['def_id']==node[1]
 assert dec(srcrow,hc)==dec(outrow,out_hc),node
assert set(out_hc)<=set(hc)
assert all(dec(hc[i],hc)==dec(out_hc[i],out_hc) for i in out_hc)
# Compare every other decoded field: allowed changes are five declaration slot arrays,
# item_names, short_names and ordered_decls; assoc item names/files/options preserved.
orig_dec=dec(raw,hc); out_dec=dec(outraw,out_hc)
allowed={*GROUPS.values(),'item_names','short_names','ordered_decls'}
for k in d:
 if k not in allowed: assert orig_dec['translated'][k]==out_dec['translated'][k],k
assert orig_dec['translated']['assoc_item_names']==out_dec['translated']['assoc_item_names']
assert orig_dec['translated']['files']==out_dec['translated']['files']

# Name maps and retained row identities for transparent review.
name_map={}
for row in d['item_names']:
 kind,i=typed_key(row,'item_names')
 if (kind,i) in reachable:name_map[f'{kind}:{i}']=''.join(x['Ident'][0]+'::' if 'Ident' in x else '' for x in row['value']).rstrip(':')
retained=[]
for kind,key in GROUPS.items():
 retained.extend({'kind':kind,'id':i,'item_name_label':name_map.get(f'{kind}:{i}'),'array_index':rows[(kind,i)][0],'body_status':('Opaque' if rows[(kind,i)][1].get('body')=='Opaque' else ('Structured' if isinstance(rows[(kind,i)][1].get('body'),dict) else 'NoFunctionBody')),'lang_item':rows[(kind,i)][1].get('item_meta',{}).get('lang_item')} for k,i in sorted(reachable) if k==kind)
# Record erased-region markers and nested-loop tagged nodes in the exact selected bodies.
def collect_paths(x,path='$',pred=lambda p,v:False,out=None):
 if out is None: out=[]
 if pred(path,x): out.append({'path':path,'value':x})
 if isinstance(x,dict):
  for k,v in x.items(): collect_paths(v,path+'.'+k,pred,out)
 elif isinstance(x,list):
  for i,v in enumerate(x): collect_paths(v,f'{path}[{i}]',pred,out)
 return out
selected_body_inventory=[]
for _,i in ROOTS:
 row=rows[('Fun',i)][1]; body=decode(row.get('body'))
 erased=collect_paths(body,pred=lambda path,v:v=='Erased')
 loops=collect_paths(body,pred=lambda path,v:isinstance(v,dict) and any('loop' in str(k).lower() for k in v))
 selected_body_inventory.append({'fun_id':i,'source_name':expected_names[i],'body_kind':list(row.get('body',{}))[0] if isinstance(row.get('body'),dict) else row.get('body'),'erased_region_occurrences':erased,'erased_region_count':len(erased),'nested_loop_tagged_node_count':len(loops),'nested_loop_tagged_nodes':loops})
selected_types=[{'type_id':i,'item_name_label':name_map.get(f'Type:{i}'),'lang_item':rows[('Type',i)][1].get('item_meta',{}).get('lang_item'),'opacity':rows[('Type',i)][1].get('item_meta',{}).get('opacity'),'local':rows[('Type',i)][1].get('item_meta',{}).get('is_local')} for k,i in sorted(reachable) if k=='Type']
report={
 'status':'mechanical_source_projection', 'input_sha256':EXPECTED,'output_sha256':sha(OUT),
 'source_body_audit_sha256':sha(source_audit/'body-audit.json'),
 'roots':[{'kind':k,'id':i,'audit_identity':expected_names.get(i)} for k,i in ROOTS],
 'root_rows_exact_identity_verified_against_audit':True,
 'closure_rows':retained,'selected_type_lang_items':selected_types,'selected_body_loop_and_erased_region_census':selected_body_inventory,'closure_counts':{k:sum(n[0]==k for n in reachable) for k in GROUPS},
 'typed_reference_occurrences':refs,'typed_reference_occurrence_count':len(refs),
 'reachable_declaration_count':len(reachable),'missing_references':missing,'unknown_typed_reference_shapes':unknown_ref_shapes,
 'ordered_decls':keep_order,'all_reachable_rows_have_original_order_entry':not ordered_missing,'ordered_missing':ordered_missing,
 'cycles_in_typed_reference_graph':[], # This records traversal termination only; graph cyclicity is separately computed below.
 'all_decoded_reachable_rows_equal_source':True,'all_output_hashcons_values_equal_original':True,
 'hashcons':{'input_definition_count':len(hc),'output_definition_count':len(out_hc),'output_ids_subset_of_original':True,'first_seen_values_reemitted':True},
 'array_lengths_preserved':{kind:len(d[key]) for kind,key in GROUPS.items()},
 'filtered_tables':{'item_names':True,'short_names':True,'assoc_item_names':'preserved unchanged in full, following R309; not interpreted as declaration rows'},
 'only_changed_translated_paths':sorted(list(allowed)),
 'implicit_prepass_dependencies':'Not projected or inferred; no extractor/tool prepass run in this mechanical task.',
 'scope':'Typed/transitive LLBC declaration projection only. No closure completeness beyond recognized references, source semantics, translation, or proof is claimed.'}
# Compute SCC/cycle report for recognized present typed-reference graph without changing projection.
state={}; stack=[]; cyc=[]
def dfs(v):
 state[v]=1;stack.append(v)
 for w in edges.get(v,()):
  if w not in reachable:continue
  if state.get(w,0)==0:dfs(w)
  elif state.get(w)==1:cyc.append(stack[stack.index(w):]+[w])
 stack.pop();state[v]=2
for node in reachable:
 if state.get(node,0)==0:dfs(node)
report['cycles_in_typed_reference_graph']=cyc
report['unknown_typed_reference_shapes']=unknown_ref_shapes
report['missing_references']=missing
report['all_reachable_rows_have_original_order_entry']=not ordered_missing
(ROOT/'projection-audit.json').write_text(json.dumps(report,indent=2)+'\n')
(ROOT/'reachable-declarations.json').write_text(json.dumps({'input_sha256':EXPECTED,'roots':[list(x) for x in ROOTS],'reachable':retained,'edges':[{'from':list(a),'to':list(b)} for a,ds in sorted(edges.items()) for b in sorted(ds)]},indent=2)+'\n')
full_rows=[{'kind':kind,'id':i,'array_index':rows[(kind,i)][0],'decoded_row':dec(rows[(kind,i)][1],hc)} for kind,i in sorted(reachable)]
(ROOT/'decoded-closure-rows.json').write_text(json.dumps({'input_sha256':EXPECTED,'rows':full_rows},indent=2)+'\n')
(ROOT/'decoded-roots.json').write_text(json.dumps({'input_sha256':EXPECTED,'roots':[{'kind':k,'id':i,'identity':expected_names[i],'decoded_row':dec(rows[(k,i)][1],hc)} for k,i in ROOTS]},indent=2)+'\n')
print(json.dumps({'closure_counts':report['closure_counts'],'reference_occurrences':len(refs),'missing':len(missing),'unknown_shapes':len(unknown_ref_shapes),'cycles':len(cyc),'ordered':len(keep_order),'output_sha256':sha(OUT)},indent=2))
