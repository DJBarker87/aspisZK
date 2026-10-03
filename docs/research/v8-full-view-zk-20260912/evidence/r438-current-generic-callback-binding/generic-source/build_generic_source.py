#!/usr/bin/env python3
"""Mechanical R438 batch closure/capture-origin inventory; no semantic claims."""
import hashlib,json,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent
LLBC=O/'input/R438GenericClosureDispatch.llbc'
raw=json.loads(LLBC.read_text()); t=raw['translated']

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,x): (O/n).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
# Resolve serialized hashcons indirections; reject missing ids/cycles.
hc={}
def walk(x,path=()):
 if isinstance(x,dict):
  if set(x)=={'HashConsedValue'}:
   pair=x['HashConsedValue']
   if not isinstance(pair,list) or len(pair)!=2 or not isinstance(pair[0],int):raise ValueError(f'malformed hashcons {path}')
   if pair[0] in hc and hc[pair[0]]!=pair[1]:raise ValueError(f'conflicting hashcons id {pair[0]}')
   hc[pair[0]]=pair[1]
  for k,v in x.items(): yield path+(k,),v;yield from walk(v,path+(k,))
 elif isinstance(x,list):
  for i,v in enumerate(x):yield path+(i,),v;yield from walk(v,path+(i,))
for p,x in walk(t):pass
def dec(x,active=()):
 if isinstance(x,dict):
  if set(x)=={'HashConsedValue'}:return dec(x['HashConsedValue'][1],active)
  if set(x)=={'Deduplicated'}:
   i=x['Deduplicated']
   if i not in hc:raise KeyError(f'missing hashcons {i}')
   if i in active:raise ValueError(f'hashcons cycle {active+(i,)}')
   return dec(hc[i],active+(i,))
  return {k:dec(v,active) for k,v in x.items()}
 if isinstance(x,list):return [dec(v,active) for v in x]
 return x

def pathstr(path):
 s=''
 for x in path:
  if isinstance(x,int):s+=f'[{x}]'
  elif s:s+='.'+str(x)
  else:s=str(x)
 return s

def stmt_nodes(x,path=()):
 if isinstance(x,dict):
  if all(k in x for k in ('span','id','kind','comments_before')):yield path,x
  for k,v in x.items():yield from stmt_nodes(v,path+(k,))
 elif isinstance(x,list):
  for i,v in enumerate(x):yield from stmt_nodes(v,path+(i,))

def place_chain(p):
 projections=[]; cur=p
 while isinstance(cur,dict) and isinstance(cur.get('kind'),dict) and set(cur['kind'])=={'Projection'}:
  pair=cur['kind']['Projection']
  if len(pair)!=2:raise ValueError('malformed projection')
  base,elem=pair;projections.append(elem);cur=base
 k=cur.get('kind') if isinstance(cur,dict) else None
 tag,payload=next(iter(k.items())) if isinstance(k,dict) and len(k)==1 else ('unknown',k)
 return {'base':{tag:payload},'projections':list(reversed(projections)),'type':cur.get('ty') if isinstance(cur,dict) else None}

def place_roots(x,path=()):
 if isinstance(x,dict):
  k=x.get('kind')
  if isinstance(k,dict) and len(k)==1 and next(iter(k)) in ('Local','Projection','Global') and 'ty' in x:
   yield path,x;return
  for key,v in x.items():yield from place_roots(v,path+(key,))
 elif isinstance(x,list):
  for i,v in enumerate(x):yield from place_roots(v,path+(i,))
def strip_child_lists(x):
 if isinstance(x,dict):return {k:strip_child_lists(v) for k,v in x.items() if k!='statements'}
 if isinstance(x,list):return [strip_child_lists(v) for v in x]
 return x

ids={'functions':[25,176,284],'types':[18,65],'trait_decls':[9],'trait_impls':[47],'globals':[18,19]}
rows={str(i):dec(t['fun_decls'][i]) for i in ids['functions']}
types={str(i):dec(t['type_decls'][i]) for i in ids['types']}
traits={str(i):dec(t['trait_decls'][i]) for i in ids['trait_decls']}
impls={str(i):dec(t['trait_impls'][i]) for i in ids['trait_impls']}
globals_={str(i):dec(t['global_decls'][i]) for i in ids['globals']}
source=t['files'][0]['contents']
if hashlib.sha256(source.encode()).hexdigest()!='4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f':raise ValueError('frozen source bytes mismatch')

# Verify exact selected identities before producing any derived table.
assert rows['25']['item_meta']['source_text'].startswith('|v:&[K]|{let mut g=K::ONE;')
assert rows['176']['item_meta']['name'][-1]['Ident'][0]=='fold'
assert rows['284']['item_meta']['source_text']=='|a,v|{let r=a.add(g.mul(*v));g=g.mul(gamma);r}'
assert rows['284']['src']['TraitImpl']['impl_ref']['id']==47
assert types['65']['item_meta']['source_text']==rows['284']['item_meta']['source_text']
assert len(types['65']['kind']['Struct'])==2

selected={'source':{'path':str((O/'input/relation_callback.rs').relative_to(O)),'sha256':hashlib.sha256((O/'input/relation_callback.rs').read_bytes()).hexdigest(),'frozen_llbc_file_id':0,'ranges':[134]},
 'llbc':{'path':str(LLBC),'sha256':sha(LLBC),'charon_version':raw.get('charon_version'),'has_errors':raw.get('has_errors')},
 'raw_rows':{'functions':{str(i):t['fun_decls'][i] for i in ids['functions']},'types':{str(i):t['type_decls'][i] for i in ids['types']},'trait_decls':{str(i):t['trait_decls'][i] for i in ids['trait_decls']},'trait_impls':{str(i):t['trait_impls'][i] for i in ids['trait_impls']},'globals':{str(i):t['global_decls'][i] for i in ids['globals']}},
 'expanded_rows':{'functions':rows,'types':types,'trait_decls':traits,'trait_impls':impls,'globals':globals_},
 'boundary':'Exact JSON LLBC rows with hash-cons indirections expanded for inspection. No semantic normalization or correspondence asserted.'}
dump('selected-source-rows.json',selected)

all_stmts=[]; call_rows=[]; assigns=[]; places=[]; event_rows=[]
for fid in ids['functions']:
 body=rows[str(fid)]['body']['Structured']
 for path,s in stmt_nodes(body['body']['statements'],('body','Structured','body','statements')):
  k=s['kind'];tag=next(iter(k)) if isinstance(k,dict) and len(k)==1 else k
  all_stmts.append({'function':fid,'statement_id':s['id'],'path':pathstr(path),'span':s['span'],'kind':tag,'payload':k})
  own=strip_child_lists(k)
  for pp,p in place_roots(own):places.append({'function':fid,'statement_id':s['id'],'statement_path':pathstr(path),'place_path':pathstr(('kind',)+pp),'place':place_chain(p),'raw_place':p})
  if tag=='Assign':
   lhs,rhs=k['Assign'];rt=next(iter(rhs)) if isinstance(rhs,dict) and len(rhs)==1 else 'unknown'
   assigns.append({'function':fid,'statement_id':s['id'],'statement_path':pathstr(path),'lhs':place_chain(lhs),'rhs_tag':rt,'rhs':rhs})
  if tag=='Call':
   c=k['Call']['call'];call_rows.append({'function':fid,'statement_id':s['id'],'statement_path':pathstr(path),'func':c['func'],'args':c['args'],'dest':c['dest'],'on_unwind':k['Call'].get('on_unwind'),'call':c})
# Preserve every path/projection-related tag found in each structured function.
EVENT={'Ref','Deref','Projection','Field','Index','Copy','Move','Aggregate','Call','Assign','Drop','StorageLive','StorageDead','Switch','Loop','Assert','PtrMetadata','RawPtr'}
def events(x,path=(),fid=None,stmtid=None):
 if isinstance(x,dict):
  if len(x)==1 and next(iter(x)) in EVENT:
   tag=next(iter(x));event_rows.append({'function':fid,'statement_id':stmtid,'path':pathstr(path),'tag':tag,'payload':x[tag]})
  for k,v in x.items():events(v,path+(k,),fid,stmtid)
 elif isinstance(x,list):
  for i,v in enumerate(x):events(v,path+(i,),fid,stmtid)
for fid in ids['functions']:
 b=rows[str(fid)]['body']['Structured']['body']['statements']
 for path,s in stmt_nodes(b,('body','Structured','body','statements')):events(s['kind'],path+('kind',),fid,s['id'])

# Statement-indexed outer initializer/capture/fold chain.
def statement(fid,sid):
 found=[x for x in all_stmts if x['function']==fid and x['statement_id']==sid]
 if len(found)!=1:raise ValueError(f'expected unique Fun{fid} statement {sid}; got {len(found)}')
 return found[0]
outer_ids=(8323,8325,8328,8333,8337,8339,8340,8347)
outer=[statement(25,sid) for sid in outer_ids]
inner_ids=(11762,11763,11766,11769,11771,11777,11785,11790,11792,11798,11801,11803)
inner=[statement(284,sid) for sid in inner_ids]
fold_trait_calls=[c for c in call_rows if c['function']==176 and isinstance(c['func'],dict) and 'Regular' in c['func'] and isinstance(c['func']['Regular'].get('kind'),dict) and 'Trait' in c['func']['Regular']['kind']]
if len(fold_trait_calls)!=1:raise ValueError(f'expected one callback trait call in Fun176 got {len(fold_trait_calls)}')
fnmut=fold_trait_calls[0]

origin={
 'frozen_source_line_134':source.splitlines()[133],
 'fun25_outer_closure_body':{'fun_id':25,'statement_ids':list(outer_ids),'statements':outer,
  'literal_path_notes':[
   'Statement 8323 moves tupled argument field 0 into Local3 (the `v` input local).',
   'Statement 8325 copies Global18 into Local4 (the `g` initialization local).',
   'Statement 8328 forms a shared Ref from Local3 projected through Deref into Local6 (slice iterator input).',
   'Statement 8333 calls Fun44 consuming Local6 and writes Local5 (iterator value).',
   'Statement 8337 forms a mutable Ref of Local4 into Local8 (capture source for Type65 field 0).',
   'Statement 8339 forms a shared Ref through receiver Local1 -> Deref -> field 0 of Adt18 -> Deref into Local9 (capture source for Type65 field 1).',
   'Statement 8340 aggregates Type65 from Move(Local8), Move(Local9) into Local7.',
   'Statement 8347 calls Fun176 with Move(Local5), Copy(Global19), Move(Local7) into Local0; complete `on_unwind` is retained.'
  ]},
 'fun176_fold_callback':{'function':176,'callback_trait_call':fnmut,
  'matching_impl_decl':{'trait_decl_9':traits['9'],'trait_impl_47':impls['47']},
  'note':'Call func trait ref, method index, args, destination and on_unwind remain verbatim in the statement record.'},
 'fun284_inner_fnmut_body':{'fun_id':284,'statement_ids':list(inner_ids),'statements':inner,
  'literal_path_notes':[
   'Statement 11769 copies through Local1 -> Deref -> Type65 field 0 -> Deref into Local8.',
   'Statement 11771 copies Local4 -> Deref into Local9 (the callback item reference path).',
   'Statement 11777 calls Fun20 with Move(Local8), Move(Local9) into Local7; unwind retained.',
   'Statement 11785 calls Fun321 with Move(Local6), Move(Local7) into Local5; unwind retained.',
   'Statement 11790 again copies through the Type65 field 0 path into Local11.',
   'Statement 11792 copies through Local1 -> Deref -> Type65 field 1 -> Deref into Local12.',
   'Statement 11798 calls Fun20 with Move(Local11), Move(Local12) into Local10; unwind retained.',
   'Statement 11801 assigns Move(Local10) through Local1 -> Deref -> Type65 field 0 -> Deref.',
   'Statement 11803 copies Local5 to return Local0.'
  ]},
 'type65_capture_layout':types['65'],
 'type18_outer_capture_layout':types['18'],
 'global18_one_row':globals_['18'],'global19_zero_row':globals_['19'],
 'all_places':places,
 'all_assignments':assigns,
 'all_calls_with_unwinds':call_rows,
 'all_statement_records':all_stmts,
 'all_reference_and_projection_events':event_rows,
 'boundary':'Serialized AST structure and source text only. This does not assert alias separation, distinct allocation, non-aliasing, lifetime validity, mutation behavior, frame semantics, or Rust-to-LLBC correspondence.'
}
dump('origin-writeback-inventory.json',origin)
dump('place-projection-table.json',places)
dump('statement-and-call-table.json',{'statements':all_stmts,'assignments':assigns,'calls_with_unwinds':call_rows,'reference_projection_events':event_rows})

# Reuse byte-identical pinned Aeneas source copies, but extract the exact branches
# that interpret Copy/Move, Ref construction, dereference/writeback, and assignment.
source_ranges={
 'InterpExpressions.ml':[(176,248,'copy_value borrow/loan cases'),(379,397,'Copy and Move context preparation'),(580,613,'Copy/Move evaluation and place updates'),(1222,1303,'Reference creation for shared and mutable borrows')],
 'InterpPaths.ml':[(100,210,'Field projection and Deref through borrows'),(290,378,'Backwards updates and Read/Write/Move policy')],
 'InterpStatements.ml':[(420,475,'Call operands and frame setup/return'),(908,990,'Assignment writes, Drop and StorageDead')]
}
ex=[]
for name,ranges in source_ranges.items():
 p=O/'pinned-aeneas'/name; lines=p.read_text().splitlines(); ex.append(f'\n## {name}, SHA256 {sha(p)}\n')
 for lo,hi,label in ranges:
  ex.append(f'\n### lines {lo}-{hi}: {label}\n'); ex.extend(f'{i:5d} {lines[i-1]}\n' for i in range(lo,min(hi,len(lines))+1))
(O/'aeneas-reference-excerpts.txt').write_text(''.join(ex))

binding=json.loads((O.parent/'generic-inventory/generic-binding-inventory.json').read_text())
assert binding['capture_sha256']==sha(LLBC)
manifest={
 'title':'R438 generic batch closure reference-origin and callback-write inventory',
 'llbc':{'path':str(LLBC),'sha256':sha(LLBC),'charon_version':raw.get('charon_version'),'has_errors':raw.get('has_errors')},
 'source':{'path':str((O/'input/relation_callback.rs').relative_to(O)),'sha256':hashlib.sha256(source.encode()).hexdigest(),'source_excerpt_line':134},
 'selected_functions':[25,176,284],'selected_types':[18,65],'selected_trait_decls':[9],'selected_trait_impls':[47],'selected_globals':[18,19],
 'source_function_ids_confirmed_from_rows':True,
 'aeneas_source_root':json.loads((O.parent/'borrow-inventory/borrow-inventory.json').read_text())['pinned_aeneas'],
 'generic_binding_inventory':{'path':str((O.parent/'generic-inventory/generic-binding-inventory.json').relative_to(O.parent)),'sha256':sha(O.parent/'generic-inventory/generic-binding-inventory.json')},
 'counts':{'statements_including_nested_unwinds':len(all_stmts),'place_chains':len(places),'assignments':len(assigns),'calls_with_unwind_fields':len(call_rows),'reference_projection_events':len(event_rows)},
 'key_facts':{
  'fun25_statement_ids':list(outer_ids),'fun176_callback_call_statement_id':fnmut['statement_id'],'fun284_statement_ids':list(inner_ids),
  'callback_dispatch_kind':fnmut['func'],'callback_args':fnmut['args'],'callback_destination':fnmut['dest'],
  'type65_fields':types['65']['kind']['Struct'],'type65_generics':types['65']['generics'],
  'fun25_fold_call':statement(25,8347),'fun25_capture_aggregate':statement(25,8340),
  'fun284_captured_field_write':statement(284,11801)
 },
 'outputs':{},
 'boundary':'This package records LLBC rows and pinned interpreter branches. It makes no conclusions about whether the references are disjoint, what allocations they point to, which frames/loans are valid, or whether source operations correspond to interpreter behavior.'
}
for n in ['selected-source-rows.json','origin-writeback-inventory.json','place-projection-table.json','statement-and-call-table.json','aeneas-reference-excerpts.txt']:
 manifest['outputs'][n]={'sha256':sha(O/n),'size_bytes':(O/n).stat().st_size}
dump('inventory.json',manifest)
readme='''# R438 generic batch closure reference origins and callback writeback

This is an additional inventory for the actual R438 capture; the sibling `borrow-inventory/` remains the separate earlier R437 Fun70/Fun112 source boundary. The exact R438 LLBC (`R438GenericClosureDispatch.llbc`, Charon 0.1.223, no errors) and frozen `relation_callback.rs` are copied under `input/`. `selected-source-rows.json` preserves both raw and hash-cons-expanded rows for Fun25, Fun176, Fun284, Type18, Type65, FnMut trait 9, impl47, and Global18/19.

`origin-writeback-inventory.json` and `place-projection-table.json` give exact statement IDs, full place chains, assignments, calls, and unwind trees. In Fun25, statement 8325 initializes Local4 by copying Global18; 8337 forms a mutable reference from Local4; 8339 forms a shared reference through receiver field 0; 8340 aggregates those moved references into the Type65 closure object; and 8347 calls Fun176 with the iterator, Global19, and that closure. Type65's two capture-field types and region parameters are preserved verbatim in the row. In Fun284, 11769 and 11790 read through receiver Deref → Type65 field 0 → Deref, 11792 reads field 1, and 11801 writes Move(Local10) back through field 0. These are serialized place/operand descriptions, not aliasing or allocation claims.

Fun176's trait callback statement row and complete `on_unwind` path are in the tables. All statement records for the selected functions and every projection occurrence are retained, including branch/loop/drop/unwind subtrees. `aeneas-reference-excerpts.txt` pins the interpreter's source implementations for Copy/Move, reference creation, borrow dereference/backward updates, frame handling, assignment, and drop. These excerpts describe interpreter code only; they are not a source-to-interpreter proof.

The Fun176 definition's source span is in `/rustc/library/core/src/slice/iter/macros.rs`; the Rust core source body is not embedded in this LLBC. No semantics, alias, allocation, lifetime, callback correctness, or source-correspondence conclusion is made.
'''
(O/'README.md').write_text(readme)
subprocess.run("find . -type f ! -path './SHA256SUMS' -print0 | sort -z | xargs -0 shasum -a 256 > SHA256SUMS",shell=True,cwd=O,check=True)
print(json.dumps({'counts':manifest['counts'],'llbc_sha':manifest['llbc']['sha256'],'fn176_callback_stmt':fnmut['statement_id']},indent=2))
