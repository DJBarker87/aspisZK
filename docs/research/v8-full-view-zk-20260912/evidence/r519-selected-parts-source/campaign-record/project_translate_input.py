#!/usr/bin/env python3
"""R519: decode using the complete original hashcons map, rewrap only original hashcons nodes, then prune function declarations to parts closure."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
SRC=(HERE.parent/'r508-selected-prepare-source/R508SelectedPrepare.llbc').resolve()
OUT=HERE/'R519SharedGammaPartsSelection.rewrapped.llbc'
AUDIT=HERE/'rewrap-projection-audit.json'
EXPECTED='600705e63cb7ba718e09a11e2da257c2fccf097173bfea00f294446265d32bc8'
KEEP={94,107,109,175,248}
sha=lambda b:hashlib.sha256(b).hexdigest()
source_bytes=SRC.read_bytes(); assert sha(source_bytes)==EXPECTED,sha(source_bytes)
source=json.loads(source_bytes); assert source['has_errors'] is False
# Build and validate complete original hashcons map before selection/pruning.
original_defs={}; original_dedup_refs=[]
def canon(x):return json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':'))
def collect_original(x):
 if isinstance(x,dict):
  if set(x)=={'HashConsedValue'}:
   i,v=x['HashConsedValue']; assert isinstance(i,int)
   if i in original_defs: assert canon(original_defs[i])==canon(v),('conflicting hashcons definition',i)
   else: original_defs[i]=v
   collect_original(v)
  elif set(x)=={'Deduplicated'}:
   i=x['Deduplicated']; assert isinstance(i,int); original_dedup_refs.append(i)
  else:
   for v in x.values():collect_original(v)
 elif isinstance(x,list):
  for v in x:collect_original(v)
collect_original(source)
missing=sorted(set(original_dedup_refs)-set(original_defs)); assert not missing,missing
active=[]
def expand_original(x,seen=()):
 if isinstance(x,dict):
  if set(x)=={'Deduplicated'}:
   i=x['Deduplicated']; assert i not in seen,('hashcons cycle',[*seen,i])
   return expand_original(original_defs[i],(*seen,i))
  if set(x)=={'HashConsedValue'}:
   i,v=x['HashConsedValue']; assert i not in seen,('hashcons wrapper cycle',[*seen,i])
   return expand_original(v,(*seen,i))
  return {k:expand_original(v,seen) for k,v in x.items()}
 if isinstance(x,list):return [expand_original(v,seen) for v in x]
 return x
expanded=expand_original(source)
# Independently derive exactly the requested declarations from the audited closure.
summary=json.loads((HERE/'dependency-summary.json').read_text())
assert summary['roots']==[['Fun',107]] and summary['missing_references']==[] and summary['unclassified_id_generics']==[]
reachable={(x['kind'],x['id']) for x in json.loads((HERE/'reachable-nodes.json').read_text())}
assert {i for k,i in reachable if k=='Fun'}==KEEP
selected_groups=[]
for group in expanded['translated']['ordered_decls']:
 k,rec=next(iter(group.items())); mode,ids=next(iter(rec.items())); ids=[ids] if mode=='NonRec' else ids
 if any((k,i) in reachable for i in ids):
  assert all((k,i) in reachable for i in ids),('partially selected recursive group',group)
  selected_groups.append(group)
expected=json.loads(json.dumps(expanded))
all_funs=expected['translated']['fun_decls']; assert all_funs[107] is not None
expected['translated']['fun_decls']=[row if i in KEEP else None for i,row in enumerate(all_funs)]
expected['translated']['ordered_decls']=selected_groups
# Re-encode each original wrapper/ref with fresh unique wrappers and fully inline its original definition.
next_id=0; fresh_ids=[]
def wrap(value):
 global next_id
 ident=next_id; next_id+=1; fresh_ids.append(ident)
 return {'HashConsedValue':[ident,serialize(value)]}
def serialize(x):
 if isinstance(x,dict):
  if set(x)=={'Deduplicated'}: return wrap(original_defs[x['Deduplicated']])
  if set(x)=={'HashConsedValue'}:
   _old,value=x['HashConsedValue']; return wrap(value)
  return {k:serialize(v) for k,v in x.items()}
 if isinstance(x,list):return [serialize(v) for v in x]
 return x
rewrapped=serialize(source)
assert fresh_ids==list(range(len(fresh_ids))) and len(fresh_ids)==len(set(fresh_ids))
# Prune only unselected function slots and ordered groups; retain all type/global/trait rows, source files, and other metadata.
fs=rewrapped['translated']['fun_decls']; assert len(fs)==len(expected['translated']['fun_decls'])
rewrapped['translated']['fun_decls']=[row if i in KEEP else None for i,row in enumerate(fs)]
rewrapped['translated']['ordered_decls']=selected_groups
out_bytes=(json.dumps(rewrapped,ensure_ascii=False,separators=(',',':'))+'\n').encode()
OUT.write_bytes(out_bytes)
# Decode the output independently, requiring fresh IDs and no unresolved Deduplicated references.
new_defs={}; new_refs=[]
def collect_new(x):
 if isinstance(x,dict):
  if set(x)=={'HashConsedValue'}:
   i,v=x['HashConsedValue']; assert isinstance(i,int) and i not in new_defs,('duplicate fresh ID',i)
   new_defs[i]=v; collect_new(v)
  elif set(x)=={'Deduplicated'}:new_refs.append(x['Deduplicated'])
  else:
   for v in x.values():collect_new(v)
 elif isinstance(x,list):
  for v in x:collect_new(v)
collect_new(rewrapped); assert not new_refs,new_refs

def expand_new(x,seen=()):
 if isinstance(x,dict):
  if set(x)=={'Deduplicated'}:raise AssertionError(('unexpected Deduplicated',x))
  if set(x)=={'HashConsedValue'}:
   i,v=x['HashConsedValue']; assert i not in seen,('new wrapper cycle',[*seen,i])
   return expand_new(v,(*seen,i))
  return {k:expand_new(v,seen) for k,v in x.items()}
 if isinstance(x,list):return [expand_new(v,seen) for v in x]
 return x
decoded=expand_new(json.loads(out_bytes)); assert decoded==expected,'decoded retained rows or preserved maps differ from the original fully-expanded projection'
# Explicit row equality census: every retained row must equal its original fully expanded row.
for table in ('type_decls','global_decls','trait_decls','trait_impls'):
 assert decoded['translated'][table]==expanded['translated'][table],table
for i in KEEP: assert decoded['translated']['fun_decls'][i]==expanded['translated']['fun_decls'][i],i
assert all(decoded['translated']['fun_decls'][i] is None for i in range(len(fs)) if i not in KEEP)
report={'status':'PASS','source_sha256':sha(source_bytes),'output_sha256':sha(out_bytes),'retained_fun_ids':sorted(KEEP),'selected_ordered_group_count':len(selected_groups),'complete_original_hashcons_definition_count':len(original_defs),'complete_original_deduplicated_reference_count':len(original_dedup_refs),'original_missing_hashcons_ids':missing,'fresh_wrapper_count':len(fresh_ids),'fresh_unique_ids':len(set(fresh_ids)),'final_hashcons_definition_count':len(new_defs),'final_deduplicated_reference_count':len(new_refs),'all_type_global_trait_rows_retained_and_equal_after_decode':True,'all_retained_fun_rows_equal_after_decode':True,'only_pruned_tables':['fun_decls','ordered_decls'],'semantic_status':'projection only; translation not yet run'}
AUDIT.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps(report,indent=2))
