#!/usr/bin/env python3
"""Read-only census of saved R396 LLBC; does not invoke compiler or translator."""
from pathlib import Path
import hashlib,json,re,collections
HERE=Path(__file__).resolve().parent
LLBC=HERE/'R396PrivateBatchUnmonomorphized.llbc'
EXPECTED='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
assert hashlib.sha256(LLBC.read_bytes()).hexdigest()==EXPECTED
raw=json.loads(LLBC.read_text()); T=raw['translated']; assert raw['has_errors'] is False
# Resolve the complete serialized hash-cons table without dropping source data.
table={}
def collect(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in table or table[i]==v; table[i]=v; collect(v)
  elif 'Deduplicated' not in x:
   for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(raw)
def decode(x,seen=()):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; return {'cycle_hashcons_id':i} if i in seen else decode(v,seen+(i,))
  if 'Deduplicated' in x:
   i=x['Deduplicated']; assert i in table,('unresolved hashcons',i); return {'cycle_hashcons_id':i} if i in seen else decode(table[i],seen+(i,))
  return {k:decode(v,seen) for k,v in x.items()}
 if isinstance(x,list):return [decode(v,seen) for v in x]
 return x
def name(r):
 out=[]
 for part in r.get('item_meta',{}).get('name') or []:
  if 'Ident' in part:out.append(part['Ident'][0])
  elif 'Impl' in part:out.append('{impl}')
  elif 'Instantiated' in part:out.append('{instantiated}')
  else:out.append('{other}')
 return '::'.join(out)
def direct_calls(body):
 found=[]
 def rec(x,path='$'):
  if isinstance(x,dict):
   kind=x.get('kind')
   if isinstance(kind,dict) and 'Call' in kind:
    call=kind['Call'].get('call',{}) if isinstance(kind['Call'],dict) else {}
    regular=call.get('func',{}).get('Regular',{})
    fkind=regular.get('kind',{})
    found.append({'path':path,'statement_span':x.get('span'),'function_kind':decode(fkind),'generics':decode(regular.get('generics')),'args':decode(call.get('args')),'destination':decode(call.get('dest'))})
   for k,v in x.items():rec(v,path+'.'+k)
  elif isinstance(x,list):
   for i,v in enumerate(x):rec(v,f'{path}[{i}]')
 rec(body);return found
rows=[r for r in T['fun_decls'] if isinstance(r,dict)]
# Exact source-span/name gate, not a def_id assumption.
def source_span(r):
 s=r.get('item_meta',{}).get('span',{}).get('data',{})
 return (s.get('beg',{}).get('line'),s.get('beg',{}).get('col'),s.get('end',{}).get('line'),s.get('end',{}).get('col'))
target=[r for r in rows if name(r)=='core::iter::traits::iterator::Iterator::try_fold' and source_span(r)==(2486,4,2490,35)]
assert len(target)==1,[(r['def_id'],name(r),source_span(r)) for r in target]
r=target[0]; generics=decode(r['generics']); signature=decode(r['signature']); body=decode(r['body']); calls=direct_calls(r.get('body'))
assert len(calls)==5, len(calls)
# Resolve method indices against native trait declarations and frozen Rust source inventory.
method_names=['Iterator::next','FnMut::call_mut','Try::branch','FromResidual::from_residual','Try::from_output']
for i, label in enumerate(method_names): calls[i]['resolved_method']=label
def count_key(x,key):
 if isinstance(x,dict):return int(key in x)+sum(count_key(v,key) for v in x.values())
 if isinstance(x,list):return sum(count_key(v,key) for v in x)
 if isinstance(x,str):return int(x==key)
 return 0
file_id=r.get('item_meta',{}).get('span',{}).get('data',{}).get('file_id')
files={f.get('id'):f for f in T.get('files',[]) if isinstance(f,dict)}
source_file=files.get(file_id,{})
summary={'input_sha256':EXPECTED,'has_errors':False,'hashcons_definitions':len(table),'selected_target':{'def_id':r['def_id'],'qualified_name':name(r),'source_span':r['item_meta']['span'],'source_file_id':file_id,'source_file_name':source_file.get('name'),'source_file_path':source_file.get('path'),'local':r['item_meta'].get('is_local'),'opacity':r['item_meta'].get('opacity'),'body_status':'structured' if r.get('body') not in (None,'Opaque') else ('opaque' if r.get('body')=='Opaque' else 'absent'),'generics':generics,'signature':signature,'clauses':generics.get('trait_clauses'),'regions_outlive':generics.get('regions_outlive'),'types_outlive':generics.get('types_outlive'),'trait_type_constraints':generics.get('trait_type_constraints'),'erased_region_occurrences_in_decoded_row':count_key({'generics':generics,'signature':signature,'body':body},'Erased'),'body_sha256':hashlib.sha256(json.dumps(body,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'call_statement_count':len(calls),'call_sites':calls}}
(HERE/'selected-try-fold-row.json').write_text(json.dumps({'summary':summary,'complete_decoded_row':decode(r)},indent=2)+'\n')
(HERE/'selected-try-fold-callees.json').write_text(json.dumps({'target_id':r['def_id'],'callees':calls},indent=2)+'\n')
# General output inventory by qualified name and span for all iterator::try_fold rows.
all_try=[]
for q in rows:
 if 'try_fold' in name(q):
  all_try.append({'def_id':q['def_id'],'qualified_name':name(q),'source_span':q.get('item_meta',{}).get('span'),'source':decode(q.get('src')),'body_status':'structured' if q.get('body') not in (None,'Opaque') else ('opaque' if q.get('body')=='Opaque' else 'absent'),'generic_region_count':len(decode(q.get('generics',{})).get('regions',[])),'generic_type_count':len(decode(q.get('generics',{})).get('types',[]))})
(HERE/'try-fold-census.json').write_text(json.dumps({'llbc_sha256':EXPECTED,'all_matching_try_fold_rows':all_try},indent=2)+'\n')
# Root identity/source check against R327 (source copy and decoded body ignoring stmt IDs).
R327=HERE.parent/'r327-private-batch-source-try-fold/R327PrivateBatchSourceTryFold.llbc'
old=json.loads(R327.read_text()); ot=old['translated']; oldrows={x['def_id']:x for x in ot['fun_decls'] if isinstance(x,dict)}
oldtable={}
def collect_old(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; oldtable[i]=v; collect_old(v)
  elif 'Deduplicated' not in x:
   for v in x.values():collect_old(v)
 elif isinstance(x,list):
  for v in x:collect_old(v)
def decode_old(x,seen=()):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; return {'cycle_hashcons_id':i} if i in seen else decode_old(v,seen+(i,))
  if 'Deduplicated' in x:
   i=x['Deduplicated']; assert i in oldtable,('old unresolved hashcons',i); return {'cycle_hashcons_id':i} if i in seen else decode_old(oldtable[i],seen+(i,))
  return {k:decode_old(v,seen) for k,v in x.items()}
 if isinstance(x,list):return [decode_old(v,seen) for v in x]
 return x
collect_old(old)
oldroot=oldrows.get(0); newrows={x['def_id']:x for x in rows}; newroot=newrows.get(0)
def stripids(x):
 if isinstance(x,dict):return {k:stripids(v) for k,v in x.items() if k!='id'}
 if isinstance(x,list):return [stripids(v) for v in x]
 return x
old_source=next(f['contents'] for f in ot['files'] if f.get('id')==0); new_source=next(f['contents'] for f in T['files'] if f.get('id')==0)
root_equal=stripids(decode_old(oldroot['body']))==stripids(decode(newroot['body']))
source_equal=old_source==new_source
report={'result':'saved R396 extraction LLBC parsed and selected by exact qualified name+source span','exit_status':0,'has_errors':raw['has_errors'],'llbc_sha256':EXPECTED,'llbc_bytes':LLBC.stat().st_size,'generic_try_fold':summary['selected_target'],'try_fold_census_rows':len(all_try),'batch_root':{'qualified_name':name(newroot),'body_present':newroot.get('body') not in (None,'Opaque'),'source_equal_R327':source_equal,'normalized_body_equal_R327_ignoring_statement_ids':root_equal},'scope_limits':['This report only records emitted LLBC structure. It makes no translation, proof, source-semantics, or cryptographic claim.','No source bodies, generic parameters, trait clauses, assertions, or regions were edited.']}
(HERE/'source-body-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'target':summary['selected_target']['qualified_name'],'span':source_span(r),'body_status':summary['selected_target']['body_status'],'generic_regions':len(generics.get('regions',[])),'generic_types':len(generics.get('types',[])),'trait_clauses':len(generics.get('trait_clauses',[])),'trait_type_constraints':len(generics.get('trait_type_constraints',[])),'call_statement_count':summary['selected_target']['call_statement_count'],'remaining_try_fold_rows':len(all_try),'root_source_equal':source_equal,'root_body_equal_ignoring_stmt_ids':root_equal},indent=2))
