#!/usr/bin/env python3
"""Read-only structural postflight for R297 LLBC. Does not invoke Charon/Aeneas/Lean."""
import collections, hashlib, json, pathlib
HERE=pathlib.Path(__file__).resolve().parent
INPUT=HERE/'R297PrivateNormBatch.llbc'
EXPECTED='6c2caba33f39adecdfc7c4facd7444ab66d505956d51036d52765b1340f84de0'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(INPUT)==EXPECTED
raw=json.loads(INPUT.read_text()); assert raw['has_errors'] is False
tr=raw['translated']
def ident(row):
 parts=[]
 for part in row.get('item_meta',{}).get('name',[]):
  if 'Ident' in part: parts.append(part['Ident'][0])
  elif 'Impl' in part:
   inner=part['Impl']
   if isinstance(inner,dict) and 'Trait' in inner: parts.append('{impl trait#'+str(inner['Trait'])+'}')
   else: parts.append('{impl}')
  elif 'Instantiated' in part: parts.append('[instantiated]')
  else: parts.append('{other}')
 return '::'.join(parts)
by={x['def_id']:x for x in tr['fun_decls'] if isinstance(x,dict)}
root=by[0]
assert root['item_meta']['is_local'] is True and root.get('body') not in (None,'Opaque')
assert root['generics']['types']==[]
def calls(body):
 found=[]
 def rec(x):
  if isinstance(x,dict):
   c=x.get('call')
   if isinstance(c,dict):
    reg=c.get('func',{}).get('Regular',{})
    fk=reg.get('kind',{}).get('Fun',{})
    if isinstance(fk,dict) and 'Regular' in fk: found.append(('regular',fk['Regular']))
    elif isinstance(fk,dict) and 'Builtin' in fk: found.append(('builtin',fk['Builtin']))
    else: found.append(('other',fk))
   for v in x.values(): rec(v)
  elif isinstance(x,list):
   for v in x: rec(v)
 rec(body); return found
root_calls=calls(root['body'])
reachable=set(); queue=[0]; edge_map={}
while queue:
 i=queue.pop(0)
 if i in reachable or i not in by: continue
 reachable.add(i); f=by[i]
 es=[target for kind,target in calls(f.get('body')) if kind=='regular'] if f.get('body') not in (None,'Opaque') else []
 edge_map[i]=es
 queue.extend(j for j in es if j not in reachable)
selected=[]
for i in sorted(set([0,3,4,12,24,36,37,38,39,40])):
 if i not in by: continue
 x=by[i]
 selected.append({'id':i,'name':ident(x),'body_status':'Opaque' if x.get('body')=='Opaque' else ('present' if x.get('body') is not None else None),'opacity':x.get('item_meta',{}).get('opacity'),'generic_type_params':x.get('generics',{}).get('types'),'generic_region_params':x.get('generics',{}).get('regions'),'trait_type_constraint_count':len(x.get('generics',{}).get('trait_type_constraints',[])),'source_origin':x.get('src')})
regular_counts=collections.Counter(target for kind,target in root_calls if kind=='regular')
builtin_counts=collections.Counter(str(target) for kind,target in root_calls if kind=='builtin')
result={
 'input':{'sha256':EXPECTED,'has_errors':False,'start_from':tr['options'].get('start_from'),'monomorphize':True},
 'root':{'fun_id':0,'name':ident(root),'local':root['item_meta']['is_local'],'body_present':True,'generic_type_params':root['generics']['types'],'generic_region_params':root['generics']['regions'],'root_order_index':next(i for i,x in enumerate(tr['ordered_decls']) if x=={'Fun':{'NonRec':0}})},
 'root_call_census':{'call_nodes':len(root_calls),'regular_call_nodes':sum(regular_counts.values()),'unique_regular_target_ids':len(regular_counts),'builtin_call_nodes':sum(builtin_counts.values()),'regular_targets':[{'fun_id':i,'count':n,'name':ident(by[i]),'body_status':'Opaque' if by[i].get('body')=='Opaque' else ('present' if by[i].get('body') is not None else None),'opacity':by[i]['item_meta'].get('opacity')} for i,n in sorted(regular_counts.items())],'builtin_target_counts':dict(builtin_counts)},
 'transitive_call_graph':{'reachable_regular_function_count':len(reachable),'reachable_fun_ids':sorted(reachable),'try_fold_reachable':[{'fun_id':i,'name':ident(by[i]),'body_status':'Opaque' if by[i].get('body')=='Opaque' else ('present' if by[i].get('body') is not None else None),'opacity':by[i]['item_meta'].get('opacity'),'generic_type_params':by[i].get('generics',{}).get('types'),'trait_type_constraint_count':len(by[i].get('generics',{}).get('trait_type_constraints',[]))} for i in sorted(reachable) if 'try_fold' in ident(by[i])]},
 'key_declarations':selected,
 'declaration_counts':{k:sum(isinstance(x,dict) for x in tr.get(k,[])) for k in ('type_decls','fun_decls','global_decls','trait_decls','trait_impls')},
 'scope':'Structural LLBC census only. No Aeneas translation, Lean compilation, or source/proof semantics conclusion.'}
(HERE/'postflight-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
