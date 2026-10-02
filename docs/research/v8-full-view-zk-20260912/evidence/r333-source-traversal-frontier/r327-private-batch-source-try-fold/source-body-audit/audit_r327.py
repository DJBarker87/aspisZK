#!/usr/bin/env python3
"""Read-only LLBC receipt/body/dependency census for R327 versus R297."""
from pathlib import Path
import collections, hashlib, json, re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
R297=ROOT.parent/'r297-private-norm-batch-monomorphized/R297PrivateNormBatch.llbc'
R327=ROOT/'R327PrivateBatchSourceTryFold.llbc'
EXPECTED_R297='6c2caba33f39adecdfc7c4facd7444ab66d505956d51036d52765b1340f84de0'
EXPECTED_R327='9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(R297)==EXPECTED_R297 and sha(R327)==EXPECTED_R327

def load(p):
 raw=json.loads(p.read_text())
 table={}
 def collect(x):
  if isinstance(x,dict):
   if 'HashConsedValue' in x:
    ident,value=x['HashConsedValue']
    assert ident not in table or table[ident]==value,('conflicting hashcons id',ident)
    table[ident]=value
    collect(value)
   elif 'Deduplicated' not in x:
    for v in x.values():collect(v)
  elif isinstance(x,list):
   for v in x:collect(v)
 collect(raw)
 def decode(x,seen=()):
  if isinstance(x,dict):
   if 'HashConsedValue' in x:
    ident,value=x['HashConsedValue']
    if ident in seen:return {'cycle_hashcons_id':ident}
    return decode(value,seen+(ident,))
   if 'Deduplicated' in x:
    ident=x['Deduplicated']
    if ident in seen:return {'cycle_hashcons_id':ident}
    assert ident in table,('unresolved hashcons',ident)
    return decode(table[ident],seen+(ident,))
   return {k:decode(v,seen) for k,v in x.items()}
  if isinstance(x,list):return [decode(v,seen) for v in x]
  return x
 return raw,table,decode

def ident(row):
 parts=[]
 for part in row.get('item_meta',{}).get('name') or []:
  if 'Ident' in part:parts.append(part['Ident'][0])
  elif 'Impl' in part:
   impl=part['Impl']
   parts.append('{impl-trait#'+str(impl['Trait'])+'}' if isinstance(impl,dict) and 'Trait' in impl else '{impl}')
  elif 'Instantiated' in part:pass
  else:parts.append('{other}')
 return '::'.join(parts)

def calls(body):
 out=[]
 def rec(x,path='$'):
  if isinstance(x,dict):
   c=x.get('call')
   if isinstance(c,dict):
    reg=c.get('func',{}).get('Regular',{})
    kind=reg.get('kind',{}).get('Fun',{})
    if isinstance(kind,dict) and 'Regular' in kind:
     out.append({'kind':'regular','target':kind['Regular'],'path':path,'call':c})
    elif isinstance(kind,dict) and 'Builtin' in kind:
     out.append({'kind':'builtin','target':kind['Builtin'],'path':path,'call':c})
    else:out.append({'kind':'other','target':kind,'path':path,'call':c})
   for k,v in x.items():rec(v,path+'.'+k)
  elif isinstance(x,list):
   for i,v in enumerate(x):rec(v,f'{path}[{i}]')
 rec(body)
 return out

def reachable(by):
 edge={i:[c['target'] for c in calls(r.get('body')) if c['kind']=='regular'] if r.get('body') not in (None,'Opaque') else [] for i,r in by.items()}
 seen=set(); todo=[0]
 while todo:
  i=todo.pop()
  if i in seen or i not in by:continue
  seen.add(i);todo.extend(j for j in edge.get(i,[]) if j not in seen)
 return seen,edge

raw297,hc297,dec297=load(R297); raw327,hc327,dec327=load(R327)
T297=raw297['translated']; T327=raw327['translated']
by297={r['def_id']:r for r in T297['fun_decls'] if isinstance(r,dict)}
by327={r['def_id']:r for r in T327['fun_decls'] if isinstance(r,dict)}
assert raw327['has_errors'] is False
assert raw297['has_errors'] is False
assert ident(by327[0])=='aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch'
assert by327[0]['item_meta']['is_local'] is True and by327[0].get('body') not in (None,'Opaque')
assert by327[0]['generics']['types']==[]
# Every added body target has stable identity and source/generic/signature metadata.
key_ids=(36,37,38,39,40)
rows=[]
for i in key_ids:
 a,b=by297[i],by327[i]
 assert ident(a)==ident(b)
 assert a.get('src')==b.get('src') and a.get('generics')==b.get('generics')
 assert dec297(a['signature'])==dec327(b['signature'])
 assert a.get('body')=='Opaque' and b.get('body') not in (None,'Opaque')
 meta={k:b.get('item_meta',{}).get(k) for k in ('is_local','opacity','span','lang_item') if k in b.get('item_meta',{})}
 # Keep compact name without the large instantiated-name payload.
 rows.append({'def_id':i,'name':ident(b),'body_status_r297':'Opaque','body_status_r327':'Structured','metadata':meta,
              'source_origin':dec327(b.get('src')),'generics':dec327(b.get('generics')),
              'signature':dec327(b.get('signature')),'decoded_body':dec327(b.get('body'))})
(HERE/'decoded-target-rows.json').write_text(json.dumps({'input_sha256':EXPECTED_R327,'hashcons_definition_count':len(hc327),'rows':rows},indent=2)+'\n')

# Full call graph reachable from batch; compare opaque leaves and direct target calls.
reach297,edges297=reachable(by297); reach327,edges327=reachable(by327)
assert reach297 <= set(by327) and reach327 <= set(by327)
key_edges={}
for i in key_ids:
 cs=calls(by327[i].get('body'))
 key_edges[str(i)]={
  'name':ident(by327[i]),
  'callee_edges':[{'target_id':c['target'],'name':ident(by327[c['target']]) if c['target'] in by327 else None,
                   'target_body_status':'Opaque' if by327.get(c['target'],{}).get('body')=='Opaque' else ('Structured' if by327.get(c['target'],{}).get('body') is not None else 'missing'),
                   'generics':dec327(c['call']['func']['Regular'].get('generics',{})),
                   'call_arguments':dec327(c['call'].get('args',[])),
                   'destination':dec327(c['call'].get('dest'))} for c in cs if c['kind']=='regular'],
  'builtin_call_ids':[str(c['target']) for c in cs if c['kind']=='builtin']}
(HERE/'typed-dependencies.json').write_text(json.dumps({'llbc_sha256':EXPECTED_R327,'callee_edges_from_new_bodies':key_edges},indent=2)+'\n')

opaque=[]
for i in sorted(reach327):
 r=by327[i]
 if r.get('body')=='Opaque':
  g=r.get('generics',{})
  opaque.append({'def_id':i,'name':ident(r),'opacity':r.get('item_meta',{}).get('opacity'),
                 'local':r.get('item_meta',{}).get('is_local'),
                 'generic_regions':len(g.get('regions',[])),'generic_types':len(g.get('types',[])),
                 'trait_clauses':len(g.get('trait_clauses',[])),
                 'regions_outlive':len(g.get('regions_outlive',[])),
                 'types_outlive':len(g.get('types_outlive',[])),
                 'trait_type_constraints':len(g.get('trait_type_constraints',[])),
                 'source_origin':dec327(r.get('src'))})
(HERE/'reachable-opaque-functions.json').write_text(json.dumps({'llbc_sha256':EXPECTED_R327,'reachable_opaque_count':len(opaque),'functions':opaque},indent=2)+'\n')

# Enumerate ADT type identifiers exposed by the five new bodies/signatures and their opaque status.
type_by={r['def_id']:r for r in T327['type_decls'] if isinstance(r,dict)}
def type_ident(r):
 parts=[]
 for p in r.get('item_meta',{}).get('name') or []:
  if 'Ident' in p:parts.append(p['Ident'][0])
  elif 'Instantiated' in p:pass
  elif 'Impl' in p:parts.append('{impl}')
 return '::'.join(parts)
type_ids=set()
def adts(x):
 if isinstance(x,dict):
  a=x.get('Adt')
  if isinstance(a,dict):
   i=a.get('id')
   if isinstance(i,dict) and isinstance(i.get('Adt'),int):type_ids.add(i['Adt'])
  for v in x.values():adts(v)
 elif isinstance(x,list):
  for v in x:adts(v)
for i in key_ids:
 r=by327[i]
 adts(dec327({'generics':r['generics'],'signature':r['signature'],'src':r.get('src'),'body':r['body']}))
types=[]
for i in sorted(type_ids):
 r=type_by.get(i)
 if r:
  types.append({'def_id':i,'name':type_ident(r),'opacity':r.get('item_meta',{}).get('opacity'),
                'local':r.get('item_meta',{}).get('is_local'),'generics':dec327(r.get('generics')),
                'source_span':r.get('item_meta',{}).get('span')})
(HERE/'reachable-typed-data.json').write_text(json.dumps({'llbc_sha256':EXPECTED_R327,'type_ids_referenced_by_changed_methods':types},indent=2)+'\n')

# Root comparison: source contents and decoded AST are equal after normalizing MIR statement IDs.
def strip_statement_ids(x):
 if isinstance(x,dict):return {k:strip_statement_ids(v) for k,v in x.items() if k!='id'}
 if isinstance(x,list):return [strip_statement_ids(v) for v in x]
 return x
root297=by297[0];root327=by327[0]
source297=next(x for x in T297['files'] if x.get('id')==0)['contents']
source327=next(x for x in T327['files'] if x.get('id')==0)['contents']
root_body_297=dec297(root297['body']);root_body_327=dec327(root327['body'])
root_body_equal=strip_statement_ids(root_body_297)==strip_statement_ids(root_body_327)
assert source297==source327 and root_body_equal
root_file_sha=hashlib.sha256(source327.encode()).hexdigest()
assert root_file_sha=='8459fc12322811b589f9a9d29bf474f3ee45e58aa13c716b8f324c2db81b160e'
(HERE/'root-source.txt').write_text('\n'.join(source327.splitlines()[60:69])+'\n')

# Input/launch provenance and resource cap checks.
cmd=json.loads((ROOT/'extract-command.json').read_text())
result=json.loads((ROOT/'result.json').read_text())
launch=json.loads((ROOT/'launch.json').read_text())
tool=(ROOT/'toolchain.txt').read_text()
after=json.loads((ROOT/'host-reservation-after.json').read_text())
prior=json.loads((ROOT/'R297-extract-command.json').read_text())
expected_added=[
 'core::iter::traits::iterator::Iterator::try_fold',
 'core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::branch',
 'core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::from_output',
 'core::ops::control_flow::{impl core::ops::try_trait::FromResidual<core::ops::control_flow::ControlFlow<_,core::convert::Infallible>> for core::ops::control_flow::ControlFlow<_,_>}::from_residual']
assert result['charon_exit_status']==0 and result['has_errors'] is False and result['llbc_exists'] is True
assert result['source_revision_recorded']==cmd['source_revision_recorded']=='d4bf07b08443136de0a11fc1fd932bd604586c2e'
assert cmd['verified_source_hashes']==result['source_hashes']==launch['verified_source_hashes']==prior['verified_source_hashes']
assert cmd['rustflags_sha256']==prior['rustflags_sha256']=='f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613'
assert cmd['start_from']==prior['start_from'] and cmd['monomorphize'] is True
assert cmd['include']==prior['include']+expected_added
assert 'nightly-2026-06-01' in tool and '14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' in tool
assert 'charon_sha256=b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c' in tool
assert launch['caps']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}
assert 'MemoryHigh=5368709120' in after['r327_slice_after'] and 'MemoryMax=7516192768' in after['r327_slice_after'] and 'MemorySwapMax=0' in after['r327_slice_after'] and 'TasksMax=128' in after['r327_slice_after']
log=(ROOT/'extract.log').read_text()
metrics={}
for key,pat in [('elapsed_wall_seconds',r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)'),('max_rss_kib',r'Maximum resident set size \(kbytes\): (\d+)'),('swaps',r'Swaps: (\d+)'),('exit_status',r'Exit status: (\d+)')]:
 m=re.search(pat,log);assert m,key;metrics[key]=m.group(1)
assert metrics=={'elapsed_wall_seconds':'0:13.47','max_rss_kib':'626232','swaps':'0','exit_status':'0'}
# Root call graph direct calls remain unchanged; newly exposed body deps come from target methods.
_,edge297=reachable(by297);_,edge327=reachable(by327)
root_direct_equal=edge297[0]==edge327[0]
assert root_direct_equal
# Only compare the five exact selected source functions here. Numeric def_ids
# are table-local positions and shift when the declaration set changes.
changed_status=[{'name':ident(by327[i]),'r297':'Opaque','r327':'Structured',
                 'r297_id':i,'r327_id':i,'comparison':'same exact name/signature/source as asserted above'}
                for i in key_ids]

# Generic R294 source-template constraints, not misreported as residual R327 free generics.
R294=ROOT.parent/'r294-private-norm-batch-extract/R294PrivateNormBatch.llbc'
raw294,hc294,dec294=load(R294)
r294fun=next(r for r in raw294['translated']['fun_decls'] if isinstance(r,dict) and r.get('def_id')==58)
g294=r294fun['generics']
constraint_template={'function_id':58,'name':ident(r294fun),'source_span':r294fun.get('item_meta',{}).get('span'),
 'body_status':'Opaque','generic_regions':len(g294['regions']),'generic_types':[x.get('name') for x in g294['types']],
 'trait_clause_count':len(g294['trait_clauses']),'trait_type_constraint_count':len(g294['trait_type_constraints']),
 'trait_clause_origins':[{'clause_id':x['clause_id'],'origin':x['origin'],'span':x['span']} for x in g294['trait_clauses']],
 'trait_type_constraint_spans':[x.get('span') for x in g294['trait_type_constraints']],
 'summary_from_R322':'Iterator Self bound, FnMut bound with Destruct at iterator.rs:2489, Try<Output=B> at 2490, and one associated Output constraint; body opaque.'}

report={
 'status':'read_only_source_body_and_dependency_audit',
 'evidence':{'R297_llbc_sha256':EXPECTED_R297,'R327_llbc_sha256':EXPECTED_R327,'R294_llbc_sha256':sha(R294),
             'R327_charon_exit':result['charon_exit_status'],'R327_has_errors':result['has_errors'],
             'R327_source_revision':result['source_revision_recorded'],'source_hashes_match_R297':True,
             'RUSTFLAGS_sha256':cmd['rustflags_sha256'],'toolchain':'nightly-2026-06-01 rustc commit 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65',
             'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128,'metrics':metrics,
             'Lean_or_Aeneas_rerun':'none; #print axioms N/A'},
 'batch_root':{'fun_id':0,'name':ident(root327),'source_file_id':0,'source_file':T327['files'][0]['name'],'source_file_sha256':root_file_sha,
               'source_lines':'61–69','root_item_is_local':root327['item_meta']['is_local'],'body_present':True,
               'decoded_root_body_equal_R297_after_ignoring_statement_ids':root_body_equal,
               'root_direct_regular_call_sequence_equal_R297':root_direct_equal,'call_sequence_length':len(edge327[0])},
 'target_methods':[{'id':i,'name':ident(by327[i]),'R297':'Opaque','R327':'Structured','generic_region_count':len(by327[i]['generics']['regions']),
                    'generic_type_count':len(by327[i]['generics']['types']),'trait_clause_count':len(by327[i]['generics']['trait_clauses']),
                    'trait_type_constraint_count':len(by327[i]['generics']['trait_type_constraints']),
                    'same_signature_generics_src_as_R297':True} for i in key_ids],
 'new_body_call_edges':{str(i):[{'callee_id':c['target'],'callee':ident(by327[c['target']]) if c['target'] in by327 else None,
                                 'callee_body':'Opaque' if by327.get(c['target'],{}).get('body')=='Opaque' else ('Structured' if by327.get(c['target'],{}).get('body') is not None else 'Absent')}
                                for c in calls(by327[i].get('body')) if c['kind']=='regular'] for i in key_ids},
 'selected_body_status_changes':changed_status,
 'declaration_id_caveat':'Def_ids are table-local positions, not stable identities across R297/R327. The former numeric-id-only status comparison was discarded: e.g. R297 Fun47 is Iterator::any closure drop_glue while R327 Fun47 is FnMut::call_mut; R297 Fun49 is reduce_u64 while R327 Fun49 is the Iterator::any closure drop_glue. Do not infer status changes by joining on numeric IDs.',
 'reachable_function_graph':{'R297_reachable_count':len(reach297),'R327_reachable_count':len(reach327),
                             'R297_opaque_reachable_count':sum(by297[i].get('body')=='Opaque' for i in reach297),
                             'R327_opaque_reachable_count':len(opaque),
                             'R327_remaining_opaque_function_ids':[r['def_id'] for r in opaque]},
 'source_constraints':{'R294_generic_iterator_try_fold':constraint_template,
                       'R327_concrete_instantiations':'Functions 36 and 38 retain one unknown region binder each but have zero free type params and zero explicit trait clauses/associated constraints in their instantiated row; body emission does not itself erase the source generic constraints.',
                       'remaining_direct_body_dependency':'Function 47 (core::ops::function::impls::<FnMut>::call_mut) is reached from Fun36 and remains Foreign/Opaque; the ordinary slice iterator next, allocation/indexing and other foreign leaves remain opaque as listed in reachable-opaque-functions.json.'},
 'prior_translation_failure':{'R303_input_sha256':EXPECTED_R297,'exit_status':2,'generated_output':False,
                              'error':'Unexpected erased region at /rustc/library/core/src/iter/traits/iterator.rs:2486:4–2490:35; Aeneas SymbolicToPureTypes.ml line 848 (keep_region at line 479).',
                              'relationship':'Historical R303 failure on R297; superseded as the first current translation failure by R330.'},
 'current_translation_failure':{'run':'R330','input_sha256':EXPECTED_R327,'exit_status':2,'generated_output':False,
                              'binary_sha256':'fff3717072567f291fc1444f52a3dc7c1f8ba4ddc5c3980e94c863cdceb60f4f',
                              'error':'Nested-loop returns require exactly one Option language item at /rustc/library/core/src/iter/traits/iterator.rs:2486:4–2490:35; R312 PrePasses.ml line 969.',
                              'metrics':{'elapsed_wall_seconds':'0:00.16','max_rss_kib':'64768','swaps':'0','exit_status':'2'},
                              'relationship':'Current first failure in the attempted R327 Aeneas translation. This report does not infer whether or how it should be changed.'},
 'limits':['LLBC structure and declaration metadata only.','No source semantic equivalence or proof premise decision.','No Aeneas translation, Lean compilation, execution, or #print axioms run.']}
(HERE/'body-audit.json').write_text(json.dumps(report,indent=2)+'\n')

# Provide root AST body/source hashes with normalized statement IDs for independent review.
root_audit={'R297_source_sha256':hashlib.sha256(source297.encode()).hexdigest(),'R327_source_sha256':root_file_sha,
            'source_text_equal':source297==source327,'R297_decoded_root_body_sha256_after_ignoring_statement_ids':hashlib.sha256(json.dumps(strip_statement_ids(root_body_297),sort_keys=True,separators=(',',':')).encode()).hexdigest(),
            'R327_decoded_root_body_sha256_after_ignoring_statement_ids':hashlib.sha256(json.dumps(strip_statement_ids(root_body_327),sort_keys=True,separators=(',',':')).encode()).hexdigest(),
            'normalized_body_equal':root_body_equal}
(HERE/'root-comparison.json').write_text(json.dumps(root_audit,indent=2)+'\n')
print(json.dumps({'has_errors':False,'exit':0,'metrics':metrics,'R297/R327 reachable': [len(reach297),len(reach327)],
 'target_methods':[(i,ident(by327[i]),'Opaque -> Structured') for i in key_ids],
 'remaining_opaque':len(opaque),'root_same_normalized_body':root_body_equal},indent=2))
