#!/usr/bin/env python3
"""Read-only extraction of R294 Slice.len and Slice.last LLBC rows."""
import hashlib, json, pathlib
ROOT=pathlib.Path(__file__).resolve().parent
SRC=ROOT.parent/'r294-private-norm-batch-extract/R294PrivateNormBatch.llbc'
PROJ=ROOT.parent/'r298-slice-last-inventory/R299SliceLastProjection.llbc'
EXPECTED='bf5ea0b6f68ab17ef73d3e721c70c9193a0682d95dcbcaf693e93187cf71da6f'
EXPECTED_PROJ='8dc807df3ff65a0bb01c27eca2a4c98de5d1f499ac566db44875dffba4050aca'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SRC)==EXPECTED and sha(PROJ)==EXPECTED_PROJ
raw=json.loads(SRC.read_text()); proj=json.loads(PROJ.read_text()); assert raw['has_errors'] is False and proj['has_errors'] is False
translated=raw['translated']; projected=proj['translated']
cons={}
def collect(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in cons or cons[i]==v; cons[i]=v; collect(v)
  elif 'Deduplicated' not in x:
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
rows={i:next(r for r in translated['fun_decls'] if isinstance(r,dict) and r.get('def_id')==i) for i in (5,12)}
type9=next(r for r in translated['type_decls'] if isinstance(r,dict) and r.get('def_id')==9)
assert rows[5]['item_meta']['lang_item']=='slice_len_fn'
assert rows[12]['item_meta']['name'][-1]['Ident'][0]=='last'
assert not any(isinstance(r,dict) and r.get('def_id')==5 for r in projected['fun_decls'])
assert any(isinstance(r,dict) and r.get('def_id')==12 for r in projected['fun_decls'])
assert any(isinstance(r,dict) and r.get('def_id')==9 for r in projected['type_decls'])
positions={}
for ix,entry in enumerate(translated['ordered_decls']):
 for kind,payload in entry.items():
  if isinstance(payload,dict) and 'NonRec' in payload: positions[(kind,payload['NonRec'])]=ix
fun12=decode(rows[12]); metadata_paths=[]
def walk(x,path='$'):
 if x=='PtrMetadata': metadata_paths.append(path)
 if isinstance(x,dict):
  for k,v in x.items(): walk(v,path+'.'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x): walk(v,f'{path}[{i}]')
walk(fun12['body'])
assert len(metadata_paths)==2,metadata_paths
body_stmts=fun12['body']['Structured']['body']['statements']
assert body_stmts[3]['span']['data']['beg']=={'line':282,'col':15}
assert body_stmts[8]['span']['data']['beg']=={'line':282,'col':20}
fun5=decode(rows[5]); assert fun5['body']=='Opaque' and fun5['item_meta']['opacity']=='Foreign'
# The opaque slice_len_fn signature has no declaration-valued function or ADT
# references in the hash-cons-expanded row.
fun_refs=[]; adt_refs=[]
def collect_decl_refs(x,path='$'):
 if isinstance(x,dict):
  if isinstance(x.get('Fun'),dict) and set(x['Fun'])=={'Regular'}:
   fun_refs.append({'path':path+'.Fun.Regular','id':x['Fun']['Regular']})
  if set(x)=={'Adt'} and isinstance(x['Adt'],int):
   adt_refs.append({'path':path+'.Adt','id':x['Adt']})
  for k,v in x.items(): collect_decl_refs(v,path+'.'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x): collect_decl_refs(v,f'{path}[{i}]')
collect_decl_refs(fun5)
assert not fun_refs and not adt_refs,(fun_refs,adt_refs)
# R300 was authorized on the exact projection; its retained LLBC row shape is unchanged.
row299=next(r for r in projected['fun_decls'] if isinstance(r,dict) and r.get('def_id')==12)
assert decode(row299)==fun12
out={'source':{'path':str(SRC),'sha256':sha(SRC),'has_errors':raw['has_errors']},'projection':{'path':str(PROJ),'sha256':sha(PROJ),'has_errors':proj['has_errors'],'ordered_decls':projected['ordered_decls']},'hashcons_definition_count':len(cons),'original_ordered_declaration_positions':{'Type9':positions[('Type',9)],'Fun5':positions[('Fun',5)],'Fun12':positions[('Fun',12)]},'rows':{'Type9':decode(type9),'Fun5_slice_len':fun5,'Fun12_slice_last':fun12},'fun12_ptr_metadata_paths':metadata_paths,'fun12_statement_shapes':{'direct_metadata_use_assign_stmt3':body_stmts[3],'ref_with_ptr_metadata_stmt8':body_stmts[8]},'projection_retention':{'Type9':True,'Fun5_slice_len':False,'Fun12_slice_last':True,'retained_fun12_decoded_equal_to_source':True},'mechanical_closure_summary':{'R298_source_typed_edge_Fun12_to_Type9':True,'Fun5_regular_fun_refs':fun_refs,'Fun5_adt_refs':adt_refs,'R294_Fun5_slice_len_has_no_regular_fun_or_adt_declaration_references':True,'additional_prepass_candidate':{'Fun':5,'lang_item':'slice_len_fn','introduced_call_is_not_an_original_LLBC_edge':True}},'scope':'Read-only LLBC row extraction and shape comparison; no translation rerun, source edit, or semantic conclusion.'}
(ROOT/'llbc-shapes.json').write_text(json.dumps(out,indent=2)+'\n')
(ROOT/'decoded-rows.json').write_text(json.dumps({'Type9':decode(type9),'Fun5':fun5,'Fun12':fun12},indent=2)+'\n')
print(json.dumps({'input_sha256':sha(SRC),'projection_sha256':sha(PROJ),'positions':out['original_ordered_declaration_positions'],'ptr_metadata_paths':metadata_paths,'fun5_retained_in_projection':False,'fun12_retained_and_decoded_equal':True},indent=2))
