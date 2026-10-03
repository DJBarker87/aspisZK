#!/usr/bin/env python3
"""Read-only inventory of R440 selected batch execution ordered groups and pinned typed dependencies."""
import json, hashlib, pathlib, collections, copy
O=pathlib.Path(__file__).resolve().parent
SRC=O/'input/R440ActualMonoClosure.llbc'
PIN=O.parent/'pinned-charon/reorder_decls.rs'
EXPECTED='01cd5ddc7086bba5f4e92802f90e59cce4034cf519d495ec35f925b91a6f033d'
PIN_EXPECTED='8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SRC)==EXPECTED,sha(SRC)
assert sha(PIN)==PIN_EXPECTED,sha(PIN)
raw=json.loads(SRC.read_text()); t=raw['translated']; assert raw['has_errors'] is False
TABLES={'Type':'type_decls','Fun':'fun_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}
rows={}
for kind,table in TABLES.items():
 for idx,row in enumerate(t[table]):
  if row is not None: rows[(kind,idx)]=row
# Capture the full original group list and a readable index/member expansion.
groups=t['ordered_decls']; members=[]
for pos,g in enumerate(groups):
 assert isinstance(g,dict) and len(g)==1, (pos,g)
 kind,rec=next(iter(g.items())); assert isinstance(rec,dict) and len(rec)==1,(pos,g)
 rec_kind,ids=next(iter(rec.items())); assert rec_kind in ('NonRec','Rec')
 ids=ids if isinstance(ids,list) else [ids]
 for i in ids:
  assert (kind,i) in rows,('ordered item missing',pos,kind,i)
  members.append({'group_index':pos,'kind':kind,'recursion':rec_kind,'id':i,'name':rows[(kind,i)]['item_meta']['name'],'is_local':rows[(kind,i)]['item_meta']['is_local'],'opacity':rows[(kind,i)]['item_meta']['opacity']})
(O/'original-ordered-decls.json').write_text(json.dumps(groups,indent=2,sort_keys=True)+'\n')
(O/'ordered-group-members.json').write_text(json.dumps(members,indent=2,sort_keys=True)+'\n')
# Build a strict hash-cons table and expand only for traversal; source LLBC bytes stay intact.
hc={}
def collect(x):
 if isinstance(x,dict):
  if set(x)=={'HashConsedValue'}:
   q=x['HashConsedValue']; assert isinstance(q,list) and len(q)==2 and isinstance(q[0],int)
   assert q[0] not in hc or hc[q[0]]==q[1],('hashcons collision',q[0]);hc[q[0]]=q[1]
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(raw)
def expand(x,active=()):
 if isinstance(x,dict):
  if set(x)=={'HashConsedValue'}: return expand(x['HashConsedValue'][1],active)
  if set(x)=={'Deduplicated'}:
   i=x['Deduplicated']; assert i in hc,('missing hashcons',i); assert i not in active,('hashcons cycle',active+(i,))
   return expand(hc[i],active+(i,))
  return {k:expand(v,active) for k,v in x.items()}
 if isinstance(x,list):return [expand(v,active) for v in x]
 return x
# ItemSource and ItemMeta are ignored by the pinned visitor. TraitDecls use a
# special visitor, matching the exact field list at pinned reorder_decls.rs:339-401.
def visited_fields(node,row):
 if node[0]=='Fun':
  return {'def_id':row.get('def_id'),'generics':row.get('generics'),'signature':row.get('signature'),'body':row.get('body')}
 if node[0]=='TraitDecl':
  out={k:row.get(k) for k in ('def_id','generics','implied_clauses','types','vtable')}
  out['consts']=[{'ty':c.get('ty'),'default':c.get('default')} for c in row.get('consts',[]) if c is not None]
  out['methods']=[{'params':m.get('params'),'signature':m.get('skip_binder',{}).get('signature'),'default':m.get('skip_binder',{}).get('default')} for m in row.get('methods',[]) if m is not None]
  return out
 return {k:v for k,v in row.items() if k not in ('item_meta','item_source','src')}

def typed_refs(x,node,path=(),out=None,unknown=None,generic_census=None):
 if out is None:out=[]
 if unknown is None:unknown=[]
 if generic_census is None:generic_census=[]
 if isinstance(x,dict):
  # Charon ref wrappers are classified by their enclosing field/variant, not
  # merely by the spelling of the integer ID.
  if isinstance(x.get('Fun'),dict) and set(x['Fun'])=={'Regular'} and isinstance(x['Fun']['Regular'],int):
   out.append(('Fun',x['Fun']['Regular'],path+('Fun','Regular')))
  if isinstance(x.get('Global'),int):out.append(('Global',x['Global'],path+('Global',)))
  if isinstance(x.get('Global'),dict) and isinstance(x['Global'].get('id'),int) and 'generics' in x['Global']:
   out.append(('Global',x['Global']['id'],path+('Global','id')))
  if isinstance(x.get('TraitImpl'),dict) and isinstance(x['TraitImpl'].get('id'),int) and 'generics' in x['TraitImpl']:
   out.append(('TraitImpl',x['TraitImpl']['id'],path+('TraitImpl','id')))
  # Trait implementation references are also used by implied_trait_refs.
  if isinstance(x.get('kind'),dict) and isinstance(x['kind'].get('TraitImpl'),dict):
   q=x['kind']['TraitImpl'];out.append(('TraitImpl',q['id'],path+('kind','TraitImpl','id')))
  # ADT references use an explicit Adt ID wrapper.
  if isinstance(x.get('id'),dict) and set(x['id'])=={'Adt'} and isinstance(x['id']['Adt'],int):out.append(('Type',x['id']['Adt'],path+('id','Adt')))
  if path[-1:] == ('vtable',) and isinstance(x.get('id'),int) and isinstance(x.get('generics'),dict):out.append((('Global' if node[0]=='TraitImpl' else 'Type'),x['id'],path+('id',)))
  if node[0]=='TraitImpl' and path[-1:] == ('consts',) and isinstance(x.get('id'),int) and isinstance(x.get('generics'),dict):out.append(('Global',x['id'],path+('id',)))
  if set(x)=={'Adt'} and isinstance(x['Adt'],int):out.append(('Type',x['Adt'],path+('Adt',)))
  # Trait declaration references have two serialized forms in this closure:
  # direct impl_trait/trait_ref refs, and a binder-wrapped trait_decl_ref.
  for key in ('trait_ref','impl_trait'):
   q=x.get(key)
   if isinstance(q,dict) and isinstance(q.get('id'),int) and 'generics' in q:out.append(('TraitDecl',q['id'],path+(key,'id')))
  q=x.get('trait_decl_ref')
  if isinstance(q,dict):
   b=q.get('skip_binder')
   if isinstance(b,dict) and isinstance(b.get('id'),int) and 'generics' in b:out.append(('TraitDecl',b['id'],path+('trait_decl_ref','skip_binder','id')))
  # An impl's associated method binder names the corresponding Fun declaration.
  if node[0]=='TraitImpl' and len(path)>=3 and path[-3]=='methods' and path[-1]=='skip_binder' and isinstance(x.get('id'),int) and 'generics' in x:
   out.append(('Fun',x['id'],path+('id',)))
  # Trait declaration defaults are associated globals/functions, not method
  # declaration IDs. The pinned visitor inserts their IDs explicitly.
  if node[0]=='TraitDecl' and path and path[-1]=='default' and isinstance(x.get('id'),int) and 'generics' in x:
   kind='Global' if 'consts' in path else 'Fun'
   out.append((kind,x['id'],path+('id',)))
  if 'trait_' in path and path[-1:] == ('skip_binder',) and isinstance(x.get('id'),int) and 'generics' in x:
   out.append(('TraitDecl',x['id'],path+('id',)))
  # Fail closed on every int-ID + generic-args record that was not assigned
  # by one of the source-shaped cases above.
  if isinstance(x.get('id'),int) and isinstance(x.get('generics'),dict):
   ref_kind=None
   if path[-1:] == ('Global',) or (node[0]=='TraitImpl' and 'consts' in path):ref_kind='Global'
   elif path[-1:] == ('TraitImpl',):ref_kind='TraitImpl'
   elif path[-1:] in [('trait_ref',),('impl_trait',)] or ('trait_decl_ref' in path and path[-1:] == ('skip_binder',)) or ('trait_' in path and path[-1:] == ('skip_binder',)):ref_kind='TraitDecl'
   elif path[-1:] == ('vtable',):ref_kind='Global' if node[0]=='TraitImpl' else 'Type'
   elif node[0]=='TraitImpl' and len(path)>=3 and path[-3]=='methods' and path[-1:] == ('skip_binder',):ref_kind='Fun'
   elif node[0]=='TraitDecl' and path[-1:] == ('default',):ref_kind='Global' if 'consts' in path else 'Fun'
   if ref_kind is None:unknown.append({'node':list(node),'path':list(path),'object_keys':sorted(x)})
   else:generic_census.append({'from':list(node),'path':list(path),'declared_reference_kind':ref_kind,'id':x['id'],'generic_arity':{k:len(v) for k,v in x['generics'].items() if isinstance(v,list)}})
  for k,v in x.items():typed_refs(v,node,path+(k,),out,unknown,generic_census)
 elif isinstance(x,list):
  for i,v in enumerate(x):typed_refs(v,node,path+(i,),out,unknown,generic_census)
 # Exact duplicate occurrence records (the parent ADT node and its explicit
 # `id` wrapper can expose the same visitor edge) are retained once per path.
 dedup=[];seen=set()
 for e in out:
  key=(e[0],e[1],e[2])
  if key not in seen:seen.add(key);dedup.append(e)
 return dedup,unknown,generic_census
ROOTS=[('Fun',29)]
assert all(root in rows for root in ROOTS)
all_ordered={(m['kind'],m['id']) for m in members}
visited=set(); active=[]; edges=[]; missing=[]; refs_by_node={}
generic_id_ref_census=[]; unclassified_id_generic=[]
parent_impl={('Fun',284):47}
parent_trait={}
def visit(node):
 if node in visited:return
 assert node in rows,('missing root/dependency row',node)
 visited.add(node); row=expand(rows[node])
 # ItemSource is not traversed for dependency edges, but pinned visitor setup
 # uses parent_info to suppress the parent impl/trait references.
 src=row.get('src')
 if isinstance(src,dict) and 'TraitImpl' in src:
  parent_impl[node]=src['TraitImpl']['impl_ref']['id']
 elif isinstance(src,dict) and 'TraitDecl' in src:
  parent_trait[node]=src['TraitDecl']['trait_ref']['id']
 scan=visited_fields(node,row)
 refs,unknown,generic_census=typed_refs(scan,node); refs_by_node[node]=refs
 generic_id_ref_census.extend(generic_census)
 unclassified_id_generic.extend(unknown)
 assert not unknown,('unclassified id+generics records',unknown)
 for kind,i,path in refs:
  target=(kind,i)
  # Preserve the edge record, including references the pinned visitor suppresses.
  suppressed=(kind=='TraitImpl' and parent_impl.get(node)==i) or (kind=='TraitDecl' and parent_trait.get(node)==i)
  available=target in rows
  edges.append({'from':list(node),'to':list(target),'path':list(path),'available_row':available,'in_original_ordered_groups':target in all_ordered,'pinned_parent_suppressed':suppressed})
  if not available:
   missing.append({'from':list(node),'to':list(target),'path':list(path)})
  elif not suppressed and target not in visited:
   if target in active:continue
   visit(target)
# Pinned visitor adds the Fun self ID first, then visits type refs; self-cycle
# handling does not affect reachable membership, so the graph inventory retains it.
for root in ROOTS:visit(root)
reachable_ordered=[m for m in members if (m['kind'],m['id']) in visited]
not_ordered=[{'kind':k,'id':i,'name':rows[(k,i)]['item_meta']['name']} for k,i in sorted(visited) if (k,i) not in all_ordered]
not_reached=[m for m in members if (m['kind'],m['id']) not in visited]
group_pos={(m['kind'],m['id']):m['group_index'] for m in members}
order_violations=[e for e in edges if e['available_row'] and not e['pinned_parent_suppressed'] and tuple(e['from']) in visited and tuple(e['to']) in visited and e['from']!=e['to'] and group_pos.get(tuple(e['to']),10**9)>=group_pos.get(tuple(e['from']),-1)]
# Aeneas has a second method-selection pass beyond Charon's ordered dependency
# visitor. Inventory source-associated methods and TraitMethod function pointers.
selected_source_methods=[]; trait_method_fnptrs=[]
for kind,i in sorted(visited):
 if kind=='Fun':
  f=rows[(kind,i)]; s=f.get('src') or {}
  for sk,sv in s.items() if isinstance(s,dict) else []:
   if sk in ('TraitImpl','TraitDecl') and isinstance(sv,dict):
    tref=sv.get('trait_ref',{})
    if isinstance(tref,dict) and isinstance(tref.get('id'),int):
     item=sv.get('item_id',{}); meth=item.get('Method') if isinstance(item,dict) else None
     if isinstance(meth,int):selected_source_methods.append({'fun_id':i,'source_kind':sk,'parent_id':sv.get('impl_ref',{}).get('id') if sk=='TraitImpl' else tref.get('id'),'trait_decl_id':tref['id'],'method_id':meth,'source_path':['src',sk]})
  decoded=expand(f)
  def find_trait_method(x,path=()):
   if isinstance(x,dict):
    kindval=x.get('kind')
    if isinstance(kindval,dict) and isinstance(kindval.get('Trait'),list) and len(kindval['Trait'])==2:
     tr,m=kindval['Trait']; tref=tr.get('trait_decl_ref',{}).get('skip_binder',{}) if isinstance(tr,dict) else {}
     if isinstance(tref,dict) and isinstance(tref.get('id'),int):trait_method_fnptrs.append({'fun_id':i,'trait_decl_id':tref['id'],'method_id':m,'path':list(path+('kind','Trait'))})
    for k,v in x.items():find_trait_method(v,path+(k,))
   elif isinstance(x,list):
    for j,v in enumerate(x):find_trait_method(v,path+(j,))
  find_trait_method(decoded.get('body'))
trait_method_rows=[]
for kind,i in sorted(visited):
 if kind=='TraitDecl':
  for mid,m in enumerate(rows[(kind,i)].get('methods',[])):
   if m is not None:trait_method_rows.append({'trait_decl_id':i,'method_slot':mid,'kind':m.get('kind'),'name':m.get('skip_binder',{}).get('name'),'source_item_meta':m.get('skip_binder',{}).get('item_meta')})
# Specific marker/raw-pointer declarations if reachable or present, as a structural census.
def name_text(n):return json.dumps(n,ensure_ascii=False)
markers=[]
for node,row in rows.items():
 s=name_text(row.get('item_meta',{}).get('name',[]))
 if node[0]=='Type' and ('NonNull' in s or 'Pattern' in s or 'RawPtr' in s or 'RawConstPtr' in s):
  markers.append({'kind':node[0],'id':node[1],'name':row['item_meta']['name'],'in_ordered_groups':node in all_ordered,'reachable_from_roots':node in visited})
# Write unchanged root rows and comprehensive reports.
(O/'selected-root-rows.json').write_text(json.dumps({'source_sha256':sha(SRC),'roots':{f'{k}{i}':rows[(k,i)] for k,i in ROOTS}},indent=2,sort_keys=True)+'\n')
(O/'dependency-edges.json').write_text(json.dumps(edges,indent=2,sort_keys=True)+'\n')
(O/'reachable-groups.json').write_text(json.dumps(reachable_ordered,indent=2,sort_keys=True)+'\n')
reachable_nodes=[]
for k,i in sorted(visited):
 r=rows[(k,i)]; meta=r.get('item_meta',{}); pos=group_pos.get((k,i))
 reachable_nodes.append({'kind':k,'id':i,'group_index':pos,'name':meta.get('name'),'source_text':meta.get('source_text'),'is_local':meta.get('is_local'),'opacity':meta.get('opacity'),'row_body_kind':next(iter(r.get('body',{})),None) if isinstance(r.get('body'),dict) else None})
(O/'reachable-nodes.json').write_text(json.dumps(reachable_nodes,indent=2,sort_keys=True)+'\n')
(O/'aeneas-trait-method-selection.json').write_text(json.dumps({'source_associated_methods':selected_source_methods,'function_pointer_trait_methods':trait_method_fnptrs,'methods_embedded_in_selected_trait_decl_rows':trait_method_rows,'source_rule':'Pinned Aeneas Interp.ml compute_contexts visitor: extracted function ItemSource TraitImplItem/TraitDeclItem adds a trait method; function-pointer kind TraitMethod adds a method; then all methods of each selected TraitDecl row are added before filtering that row. This is translator-selection metadata only.'},indent=2,sort_keys=True)+'\n')
summary={'input_sha256':sha(SRC),'pinned_reorder_source_sha256':sha(PIN),'pinned_source_path':'/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/src/transform/add_missing_info/reorder_decls.rs','ordered_group_count':len(groups),'ordered_member_count':len(members),'group_kind_counts':dict(collections.Counter(m['kind'] for m in members)),'roots':[list(x) for x in ROOTS],'root_group_indices':{f'{k}{i}':group_pos[(k,i)] for k,i in ROOTS},'reachable_node_count':len(visited),'reachable_group_member_count':len(reachable_ordered),'reachable_kind_counts':dict(collections.Counter(m['kind'] for m in reachable_ordered)),'reachable_but_not_ordered':not_ordered,'ordered_but_not_reachable_count':len(not_reached),'ordered_but_not_reachable':not_reached,'edge_count':len(edges),'generic_id_reference_count':len(generic_id_ref_census),'generic_id_references':generic_id_ref_census,'unclassified_id_generics':unclassified_id_generic,'missing_references':missing,'parent_suppression_edge_count':sum(e['pinned_parent_suppressed'] for e in edges),'markers_rawptr_pattern':markers,'original_order_dependency_violations':len(order_violations),'groups_only_filter_preserves_all_reachable':not not_ordered,'group_field':'translated.ordered_decls (this LLBC has no translated.declarations field; pinned OfJson.ml maps ordered_decls to OCaml crate.declarations)','source_scope':'Pinned DepsForItem traversal as mechanically reconstructed from its exact visitor field handling; Aeneas method-selection metadata separately recorded. JSON/group inventory only, with no AST modification or source-semantics claim.'}
(O/'order-violations.json').write_text(json.dumps(order_violations,indent=2,sort_keys=True)+'\n')
(O/'dependency-summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:summary[k] for k in ('ordered_group_count','ordered_member_count','group_kind_counts','roots','reachable_node_count','reachable_kind_counts','reachable_but_not_ordered','edge_count','missing_references','groups_only_filter_preserves_all_reachable')},indent=2))
