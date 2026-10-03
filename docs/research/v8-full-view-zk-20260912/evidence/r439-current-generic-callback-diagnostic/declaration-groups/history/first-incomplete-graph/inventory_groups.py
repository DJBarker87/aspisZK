#!/usr/bin/env python3
"""Read-only inventory of R438 ordered groups and pinned typed dependencies."""
import json, hashlib, pathlib, collections, copy
O=pathlib.Path(__file__).resolve().parent
SRC=O/'input/R438GenericClosureDispatch.llbc'
PIN=O/'pinned-charon/reorder_decls.rs'
EXPECTED='76eefed780e23eb3243413b913e935dc7a9b661bceeb0fc0346668621ab07fb6'
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
  out['consts']=[{'ty':c.get('ty'),'default':c.get('default')} for c in row.get('consts',[])]
  out['methods']=[{'params':m.get('params'),'signature':m.get('skip_binder',{}).get('signature'),'default':m.get('skip_binder',{}).get('default')} for m in row.get('methods',[])]
  return out
 return {k:v for k,v in row.items() if k not in ('item_meta','item_source','src')}

def typed_refs(x,path=(),out=None):
 if out is None:out=[]
 if isinstance(x,dict):
  if 'Fun' in x:
   f=x['Fun']
   if isinstance(f,dict) and set(f)=={'Regular'} and isinstance(f['Regular'],int):out.append(('Fun',f['Regular'],path+('Fun','Regular')))
  if 'Global' in x:
   g=x['Global']
   if isinstance(g,int):out.append(('Global',g,path+('Global',)))
   elif isinstance(g,dict) and isinstance(g.get('id'),int) and 'generics' in g:out.append(('Global',g['id'],path+('Global','id')))
  if 'TraitImpl' in x:
   q=x['TraitImpl']
   if isinstance(q,dict) and isinstance(q.get('id'),int) and 'generics' in q:out.append(('TraitImpl',q['id'],path+('TraitImpl','id')))
  # ADT type declaration references; references occur in both outer type
  # constructors and explicit IDs. Deduplicate identical edge/path records later.
  if isinstance(x.get('id'),dict) and set(x['id'])=={'Adt'} and isinstance(x['id']['Adt'],int):out.append(('Type',x['id']['Adt'],path+('id','Adt')))
  if set(x)=={'Adt'} and isinstance(x['Adt'],int):out.append(('Type',x['Adt'],path+('Adt',)))
  for key in ('trait_ref','trait_decl_ref'):
   q=x.get(key)
   if isinstance(q,dict) and isinstance(q.get('id'),int):out.append(('TraitDecl',q['id'],path+(key,'id')))
  for key in ('impl_ref','impl_trait'):
   q=x.get(key)
   if isinstance(q,dict) and isinstance(q.get('id'),int):out.append(('TraitImpl',q['id'],path+(key,'id')))
  for k,v in x.items():typed_refs(v,path+(k,),out)
 elif isinstance(x,list):
  for i,v in enumerate(x):typed_refs(v,path+(i,),out)
 return out
ROOTS=[('Fun',284),('TraitImpl',47)]
assert ROOTS[0] in rows and ROOTS[1] in rows
all_ordered={(m['kind'],m['id']) for m in members}
visited=set(); active=[]; edges=[]; missing=[]; refs_by_node={}
parent_impl={('Fun',284):47}
parent_trait={}
def visit(node):
 if node in visited:return
 assert node in rows,('missing root/dependency row',node)
 visited.add(node); row=expand(rows[node]); scan=visited_fields(node,row)
 refs=typed_refs(scan); refs_by_node[node]=refs
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
summary={'input_sha256':sha(SRC),'pinned_reorder_source_sha256':sha(PIN),'pinned_source_path':'R288 pinned reorder_decls.rs, same full hash as R267/R284 source pin','ordered_group_count':len(groups),'ordered_member_count':len(members),'group_kind_counts':dict(collections.Counter(m['kind'] for m in members)),'roots':[list(x) for x in ROOTS],'reachable_node_count':len(visited),'reachable_group_member_count':len(reachable_ordered),'reachable_kind_counts':dict(collections.Counter(m['kind'] for m in reachable_ordered)),'reachable_but_not_ordered':not_ordered,'ordered_but_not_reachable_count':len(not_reached),'ordered_but_not_reachable':not_reached,'edge_count':len(edges),'missing_references':missing,'parent_suppression_edge_count':sum(e['pinned_parent_suppressed'] for e in edges),'markers_rawptr_pattern':markers,'groups_only_filter_preserves_all_reachable':not not_ordered,'group_field':'translated.ordered_decls (this LLBC has no translated.declarations field)','source_scope':'Pinned DepsForItem traversal approximation from exact source logic; JSON references recorded without altering the LLBC or claiming operational/source semantics.'}
(O/'dependency-summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:summary[k] for k in ('ordered_group_count','ordered_member_count','group_kind_counts','roots','reachable_node_count','reachable_kind_counts','reachable_but_not_ordered','edge_count','missing_references','groups_only_filter_preserves_all_reachable')},indent=2))
