#!/usr/bin/env python3
"""Read-only R431 fun70 full-AST/control-flow/type inventory; no AST normalization."""
import hashlib,json,collections
from pathlib import Path
ROOT=Path.cwd(); OUT=ROOT/'.r21-scratch/r434-actual-fold-control/inventory'
INPUT=ROOT/'.r21-scratch/r431-actual-slice-construction/root-launch-a/saved-output/R431ActualSliceConstruction.llbc'
EXPECTED_SHA='df9180ee7c9959a7840d6edac0b756f007ef33ed0bd88bb36faf57a3e18f2358'
FUN_ID=70

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def dump(name,obj):(OUT/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def name_text(n):
 if not isinstance(n,list):return str(n)
 xs=[]
 for p in n:
  if isinstance(p,dict) and 'Ident' in p:xs.append(p['Ident'][0])
  elif isinstance(p,dict) and 'Impl' in p:xs.append('<impl>')
  elif isinstance(p,dict) and 'Closure' in p:xs.append('<closure>')
 return '::'.join(xs)
raw=read(INPUT); tr=raw['translated']; f=tr['fun_decls'][FUN_ID]
assert sha(INPUT)==EXPECTED_SHA and raw.get('has_errors') is False
assert name_text(f['item_meta']['name'])=='core::slice::iter::<impl>::fold'
# Resolve Charon's capture-local hash-cons and deduplicated type references while preserving source rows.
hash_defs={};conflicts=[];dedup_refs=set()
def collect(x):
 if isinstance(x,dict):
  hv=x.get('HashConsedValue')
  if isinstance(hv,list) and len(hv)==2:
   i,v=hv
   if i in hash_defs and hash_defs[i]!=v:conflicts.append(i)
   hash_defs[i]=v
  if set(x)=={'Deduplicated'}:dedup_refs.add(x['Deduplicated'])
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(tr)
assert not conflicts,sorted(set(conflicts))
missing=sorted(dedup_refs-set(hash_defs));assert not missing,missing
def resolve(x,stack=()):
 if isinstance(x,dict):
  if set(x)=={'Deduplicated'}:
   i=x['Deduplicated'];
   if i in stack:raise ValueError(f'dedup cycle {stack+(i,)}')
   return {'ResolvedDeduplicated':i,'value':resolve(hash_defs[i],stack+(i,))}
  if set(x)=={'HashConsedValue'}:
   i,v=x['HashConsedValue'];
   if i in stack:raise ValueError(f'hashcons cycle {stack+(i,)}')
   return {'ResolvedHashConsedValue':i,'value':resolve(v,stack+(i,))}
  return {k:resolve(v,stack) for k,v in x.items()}
 if isinstance(x,list):return [resolve(v,stack) for v in x]
 return x
def stmt_tag(s):
 k=s.get('kind')
 if isinstance(k,str):return k
 if isinstance(k,dict) and len(k)==1:return next(iter(k))
 return 'UNKNOWN'
def direct_refs(x,base='$'):
 refs=[]
 def walk(v,path):
  if isinstance(v,dict):
   if 'Call' in v and isinstance(v['Call'],dict):
    c=v['Call'].get('call',{})
    refs.append({'kind':'Call','path':path,'func':c.get('func'),'args':c.get('args',[]),'destination':c.get('dest'),'has_on_unwind':'on_unwind' in v['Call']})
   if 'Drop' in v and isinstance(v['Drop'],dict):
    q=v['Drop'];refs.append({'kind':'Drop','path':path,'place':q.get('place'),'fn_ptr':q.get('fn_ptr'),'has_on_unwind':'on_unwind' in q})
   for k,y in v.items():walk(y,path+'/'+str(k))
  elif isinstance(v,list):
   for i,y in enumerate(v):walk(y,f'{path}/{i}')
 walk(x,base);return refs

def operand_sites(x,base='$'):
 out=[]
 def walk(v,path):
  if isinstance(v,dict):
   for mode in ('Copy','Move','Const'):
    if mode in v and isinstance(v[mode],dict):
     payload=v[mode];p=payload.get('kind')
     if isinstance(p,dict):out.append({'mode':mode,'path':path+'/'+mode,'place':p,'ty_raw':payload.get('ty'),'ty_resolved':resolve(payload.get('ty'))})
   for k,y in v.items():walk(y,path+'/'+str(k))
  elif isinstance(v,list):
   for i,y in enumerate(v):walk(y,f'{path}/{i}')
 walk(x,base);return out

def rvalue_info(s,path):
 k=s.get('kind')
 if not isinstance(k,dict) or 'Assign' not in k:return None
 v=k['Assign'];
 if not isinstance(v,list) or len(v)!=2:raise ValueError('unrecognized Assign at '+path)
 dst,rv=v
 return {'destination_raw':dst,'destination_type_resolved':resolve(dst.get('ty')) if isinstance(dst,dict) else None,
         'destination_local_or_projection':dst.get('kind') if isinstance(dst,dict) else None,
         'rvalue_opcode':next(iter(rv)) if isinstance(rv,dict) and len(rv)==1 else 'UNKNOWN',
         'rvalue_raw':rv,'operand_sites':operand_sites(rv,path+'/rvalue'),
         'rvalue_resolved_type_fields':resolved_type_fields(rv)}
def resolved_type_fields(x):
 out=[]
 def walk(v,path='$'):
  if isinstance(v,dict):
   for k,y in v.items():
    if k=='ty':out.append({'path':path+'/ty','raw':y,'resolved':resolve(y)})
    walk(y,path+'/'+str(k))
  elif isinstance(v,list):
   for i,y in enumerate(v):walk(y,f'{path}/{i}')
 walk(x);return out

body=f['body']['Structured']['body'];locals_rows=f['body']['Structured']['locals']['locals']
# Full source rows, unmodified.
(OUT/'fun70-raw-row.json').write_text(json.dumps(f,indent=2,sort_keys=True)+'\n')
# All local types resolved independently; raw local declarations are retained alongside.
local_table=[]
for loc in locals_rows:
 local_table.append({'index':loc['index'],'name':loc.get('name'),'span':loc.get('span'),'ty_raw':loc.get('ty'),'ty_resolved':resolve(loc.get('ty'))})
dump('fun70-locals-and-types.json',{'function_id':FUN_ID,'argument_count':f['body']['Structured']['locals']['arg_count'],'locals':local_table,'hashcons_definition_count':len(hash_defs),'deduplicated_reference_count':len(dedup_refs)})
# Traverse all nested control-flow/cleanup statement arrays; full raw row is authoritative.
statements=[]; control=[]; assignments=[]; all_refs=[]; counters=collections.Counter(); op_nodes=[]; local17=[]; pointer_offsets=[]; unchecked_add=[]; deref_projections=[]; global_refs=[]
control_tags={'Switch','Loop','Assert','Call','Drop','Abort','UnwindResume','Return','Break','Continue'}
interesting_expr={'BinaryOp','UnaryOp','RawPtr','Ref','NullaryOp','Transmute','Cast','PtrMetadata','Offset','Deref'}
def walk(x,path='$'):
 if isinstance(x,dict):
  if {'id','kind','span','comments_before'}<=set(x):
   tag=stmt_tag(x); rec={'path':path,'statement_id':x['id'],'opcode':tag,'span':x.get('span'),'raw_statement':x}
   ri=rvalue_info(x,path)
   if ri is not None:rec['assignment']=ri;assignments.append({'path':path,**ri})
   statements.append(rec);counters['statement:'+tag]+=1
   if tag in control_tags:control.append(rec)
  for k,v in x.items():
   p=path+'/'+str(k)
   if k in interesting_expr:
    counters['node:'+k]+=1;op_nodes.append({'path':p,'node_tag':k,'raw_node':v})
    if k=='BinaryOp' and isinstance(v,list) and v:
     if v[0]=='Offset':pointer_offsets.append({'path':p,'raw_node':v,'parent_path':path})
     if isinstance(v[0],dict) and v[0].get('Add')=='UB':unchecked_add.append({'path':p,'raw_node':v,'parent_path':path})
   if k=='Projection' and isinstance(v,list) and len(v)==2 and v[1]=='Deref':
    deref_projections.append({'path':p,'base_place_raw':v[0],'base_place_resolved_type':resolve(v[0].get('ty')) if isinstance(v[0],dict) else None})
   if k=='Global' and isinstance(v,dict):global_refs.append({'path':p,'raw':v})
   if k=='Move' and isinstance(v,dict) and isinstance(v.get('kind'),dict) and v['kind'].get('Local')==17:
    local17.append({'path':p,'move_node':x,'move_ty_resolved':resolve(v.get('ty'))})
   walk(v,p)
 elif isinstance(x,list):
  for i,v in enumerate(x):walk(v,f'{path}/{i}')
walk(body,'fun70/body')
local17_writes=[{'path':a['path'],'destination_raw':a['destination_raw'],'destination_type_resolved':a['destination_type_resolved']}
 for a in assignments if isinstance(a.get('destination_local_or_projection'),dict) and a['destination_local_or_projection'].get('Local')==17]
# Link each regular function target to its declaration name and opacity/body form.
refs=direct_refs(body,'fun70/body')
for r in refs:
 q=r.get('func') if r['kind']=='Call' else r.get('fn_ptr')
 target=None
 if isinstance(q,dict):
  # Calls wrap a function ref in Regular; Drop stores the ref directly.
  reg=q.get('Regular') if 'Regular' in q else q
  if isinstance(reg,dict):
   kind=(reg.get('kind') or {})
   fun=kind.get('Fun') or {}
   fref=fun.get('Regular') if isinstance(fun,dict) else None
   if isinstance(fref,int):target=fref
   trait=kind.get('Trait') if isinstance(kind,dict) else None
   if isinstance(trait,list) and len(trait)==2:
    tref=trait[0]
    r['trait_dispatch']={'trait_ref_raw':tref,'method_index':trait[1],
      'trait_ref_resolved':resolve(tref),'generic_args_raw':reg.get('generics')}
    try:
     tid=resolve(tref)['value']['trait_decl_ref']['skip_binder']['id']
     mi=trait[1]
     r['trait_dispatch']['trait_decl_id']=tid
     r['trait_dispatch']['method_name']=tr['assoc_item_names'][tid]['methods'][mi]
    except (KeyError,IndexError,TypeError):
     r['trait_dispatch']['method_resolution']='unresolved by assoc_item_names'
 r['regular_function_target_id']=target
 if target is not None and target<len(tr['fun_decls']) and isinstance(tr['fun_decls'][target],dict):
  callee=tr['fun_decls'][target]
  r['target_name']=name_text((callee.get('item_meta') or {}).get('name'))
  b=callee.get('body');r['target_body_form']=list(b) if isinstance(b,dict) else b

dump('fun70-operation-table.json',{'input_path':str(INPUT.relative_to(ROOT)),'input_sha256':sha(INPUT),'function_id':FUN_ID,
 'top_level_statement_count':len(body['statements']),'all_recursive_statement_nodes':len(statements),
 'statement_rows':statements,'assignment_rows':assignments,'expression_node_counts':dict(sorted(counters.items())),
 'control_flow_error_cleanup_nodes':control,'call_and_drop_reference_nodes':refs,
 'local17_move_nodes':local17,'local17_write_sites':local17_writes,'pointer_offset_sites':pointer_offsets,'unchecked_add_sites':unchecked_add,
 'deref_projection_sites':deref_projections,'global_references':global_refs,'other_expression_nodes':op_nodes})
# Preserve globals and selected data dependencies discovered in this row.
gids=sorted({g['raw'].get('id') for g in global_refs if isinstance(g.get('raw'),dict) and isinstance(g['raw'].get('id'),int)})
selected_globals={str(i):tr['global_decls'][i] for i in gids}
fids=sorted({r['regular_function_target_id'] for r in refs if isinstance(r.get('regular_function_target_id'),int)})
# The three requested source dependencies plus both drop-glue functions are retained explicitly,
# even if an LLBC version's function-reference wrapper differs from the common Call shape.
fids=sorted(set(fids)|{114,115,116,144,145})
selected_functions={str(i):tr['fun_decls'][i] for i in fids if i<len(tr['fun_decls']) and isinstance(tr['fun_decls'][i],dict)}
# Resolve the closure FnMut dispatch only as far as native declaration metadata supports:
# TraitImpl 35 implements FnMut and implies FnOnce TraitImpl 34; Fun112 is explicitly
# named as the same closure impl's call_mut method. The impl method arrays themselves are empty.
closure_dispatch={'trait_decl_id':3,'method_index':0,'method_name':tr['assoc_item_names'][3]['methods'][0],
 'trait_impl_id':35,'trait_impl':tr['trait_impls'][35],
 'implied_fn_once_trait_impl':tr['trait_impls'][34],
 'fn112':tr['fun_decls'][112],
 'mapping_boundary':'Native names agree on closure::call_mut and the FnMut TraitImpl id, but trait_impl.methods is empty; this inventory does not derive a lowered executable body mapping.'}
# Record exact sites for UB-check configuration and all occurrences of locals 45/46.
ub_sites=[]; local45_46=[]
for node in op_nodes:
 if node['node_tag']=='NullaryOp' and isinstance(node['raw_node'],list) and node['raw_node'] and node['raw_node'][0]=='UbChecks':
  ub_sites.append({'path':node['path'],'raw_node':node['raw_node'],'resolved':resolve(node['raw_node'])})
for node in operand_sites(body,'fun70/body'):
 p=node.get('place',{})
 if isinstance(p,dict) and p.get('Local') in (45,46):local45_46.append(node)
dump('fun70-direct-dependency-rows.json',{'input_path':str(INPUT.relative_to(ROOT)),'input_sha256':sha(INPUT),'global_ids':gids,'globals':selected_globals,'regular_function_ids':fids,'functions':selected_functions,'closure_fnmut_dispatch':closure_dispatch,
 'ubchecks_sites':ub_sites,'local45_46_operand_sites':local45_46})
# Preserve structured rows for the two newly emitted helper bodies from a distinct capture.
HELPER_INPUT=ROOT/'.r21-scratch/r434-actual-fold-control/root-launch-a/saved-output/R434ActualFoldUbHelpers.llbc'
HELPER_SHA='7c03a7576da2d380749bdd48a9ded791e4563d6fb3b6834ef4d15665f479b96e'
hd=read(HELPER_INPUT); ht=hd['translated']; assert sha(HELPER_INPUT)==HELPER_SHA and hd.get('has_errors') is False
# The second extraction has an independent hash-cons namespace. Replace the active resolver
# table only after all R431 artifacts have been written.
hash_defs.clear(); dedup_refs.clear(); conflicts.clear(); collect(ht)
assert not conflicts and not sorted(dedup_refs-set(hash_defs))
helper_rows={}; helper_tables={}
for fid in (114,115):
 hf=ht['fun_decls'][fid]; assert isinstance(hf.get('body'),dict) and 'Structured' in hf['body']
 hb=hf['body']['Structured']['body']; hstat=[]; hassign=[]; hcontrol=[]; hc=collections.Counter()
 def hwalk(x,path='$'):
  if isinstance(x,dict):
   if {'id','kind','span','comments_before'}<=set(x):
    tag=stmt_tag(x); hc['statement:'+tag]+=1
    rec={'path':path,'statement_id':x['id'],'opcode':tag,'span':x.get('span'),'raw_statement':x}
    ri=rvalue_info(x,path)
    if ri is not None:rec['assignment']=ri;hassign.append({'path':path,**ri})
    hstat.append(rec)
    if tag in control_tags:hcontrol.append(rec)
   for k,v in x.items():hwalk(v,path+'/'+str(k))
  elif isinstance(x,list):
   for j,v in enumerate(x):hwalk(v,f'{path}/{j}')
 hwalk(hb,f'fun{fid}/body')
 hrefs=direct_refs(hb,f'fun{fid}/body')
 helper_rows[str(fid)]=hf
 helper_tables[str(fid)]={'function_id':fid,'name':name_text(hf['item_meta']['name']),'span':hf['item_meta'].get('span'),
  'signature_raw':hf.get('signature'),'signature_resolved':resolve(hf.get('signature')),
  'body_form':list(hf['body']),'top_level_statement_count':len(hb.get('statements',[])),
  'recursive_statement_count':len(hstat),'statement_counts':dict(sorted(hc.items())),
  'statement_rows':hstat,'assignment_rows':hassign,'control_flow_and_cleanup_rows':hcontrol,'calls_and_drops':hrefs}
dump('helper114-115-raw-rows.json',{'input_path':str(HELPER_INPUT.relative_to(ROOT)),'input_sha256':sha(HELPER_INPUT),
 'has_errors':hd.get('has_errors'),'function_ids':[114,115],'functions':helper_rows})
dump('helper114-115-operation-tables.json',{'input_path':str(HELPER_INPUT.relative_to(ROOT)),'input_sha256':sha(HELPER_INPUT),'functions':helper_tables,
 'source_capture_boundary':'These are the selectively translated helper rows from R434. Their bodies are preserved as emitted; this is not a proof or interpretation of their checks.'})
dump('helper-capture-provenance.json',{'path':str(HELPER_INPUT.relative_to(ROOT)),'sha256':sha(HELPER_INPUT),'size_bytes':HELPER_INPUT.stat().st_size,
 'result_path':str(HELPER_INPUT.parent/'result.json'),'result_sha256':sha(HELPER_INPUT.parent/'result.json'),'result':read(HELPER_INPUT.parent/'result.json'),
 'command_path':str(HELPER_INPUT.parent/'extract-command.json'),'command_sha256':sha(HELPER_INPUT.parent/'extract-command.json'),'command':read(HELPER_INPUT.parent/'extract-command.json'),
 'original_fold_capture_sha256':sha(INPUT),'note':'Separate extraction capture with source-focused helper bodies; original Fun70 fold inventory remains pinned to R431 input.'})
# Run receipt and source row identity.
result_path=INPUT.parent/'result.json'; command_path=INPUT.parent/'extract-command.json'
dump('input-provenance.json',{'input_path':str(INPUT.relative_to(ROOT)),'input_sha256':sha(INPUT),'size_bytes':INPUT.stat().st_size,
 'result_path':str(result_path.relative_to(ROOT)),'result_sha256':sha(result_path),'result':read(result_path),
 'command_path':str(command_path.relative_to(ROOT)),'command_sha256':sha(command_path),'command':read(command_path),
 'stdlib_inventory_path':'.r21-scratch/r431-actual-slice-construction/stdlib-contracts/inventory.json',
 'stdlib_inventory_sha256':sha(ROOT/'.r21-scratch/r431-actual-slice-construction/stdlib-contracts/inventory.json')})
print('functions',fids,'globals',gids,'recursive statement nodes',len(statements),'local17 move',len(local17),'offset',len(pointer_offsets),'unchecked add',len(unchecked_add),'deref',len(deref_projections))
