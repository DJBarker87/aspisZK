"""Build and audit the lead-authorized two-row LLBC projection; never translate it."""
import copy, hashlib, json, pathlib
ROOT=pathlib.Path(__file__).resolve().parent
SRC=ROOT.parent/'r294-private-norm-batch-extract/R294PrivateNormBatch.llbc'
INV=ROOT/'inventory.json'
R220=ROOT.parent/'r220-vector-reachable-projection/schema-audited-incomplete/project_schema_complete.py'
R220_SCHEMA=ROOT.parent/'r220-vector-reachable-projection/schema-source/charon-ast-reference-excerpts.txt'
PINNED=ROOT.parent/'r267-private-inverse-leaf-ordering/pinned-reorder_decls.rs'
OUT=ROOT/'R299SliceLastProjection.llbc'
EXPECTED_SRC='bf5ea0b6f68ab17ef73d3e721c70c9193a0682d95dcbcaf693e93187cf71da6f'
EXPECTED_PINNED='8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632'
EXPECTED_R220='409a2a1281ac69df671491c5d35292bce045daead39f5d73007f79a814ec4338'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SRC)==EXPECTED_SRC and sha(PINNED)==EXPECTED_PINNED and sha(R220)==EXPECTED_R220
inv=json.loads(INV.read_text())
assert inv['input_llbc_sha256']==EXPECTED_SRC
assert inv['pinned_reorder_rules_sha256']==EXPECTED_PINNED
assert inv['closure_counts']=={'Type':1,'Fun':1,'Global':0,'TraitDecl':0,'TraitImpl':0}
assert inv['cycles']==[] and inv['unknown_reference_shapes']==[]
assert inv['absent_references_filtered_by_pinned_get_item']==[]
assert inv['closure_reaches_generic_iterator_try_fold'] is False
raw=json.loads(SRC.read_text()); assert raw['has_errors'] is False
D=raw['translated']
GROUPS={'Type':'type_decls','Fun':'fun_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}
KEEP={'Type':{9},'Fun':{12},'Global':set(),'TraitDecl':set(),'TraitImpl':set()}

# Preserve hash-cons IDs/values exactly using the serializer pattern in the
# schema-audited R220 projection source; this script independently validates
# the input/output tables and decoded retained rows below.
def collect_hashcons(x,table):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   ident,value=x['HashConsedValue']
   assert ident not in table or table[ident]==value,('conflicting hashcons id',ident)
   table[ident]=value; collect_hashcons(value,table)
  elif 'Deduplicated' not in x:
   for v in x.values(): collect_hashcons(v,table)
 elif isinstance(x,list):
  for v in x: collect_hashcons(v,table)
ORIG_HC={}; collect_hashcons(raw,ORIG_HC)

def decode(table,x,seen=()):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   ident,value=x['HashConsedValue']
   if ident in seen: return {'cycle_hashcons_id':ident}
   return decode(table,value,seen+(ident,))
  if 'Deduplicated' in x:
   ident=x['Deduplicated']
   if ident in seen: return {'cycle_hashcons_id':ident}
   assert ident in table,('unresolved hashcons',ident)
   return decode(table,table[ident],seen+(ident,))
  return {k:decode(table,v,seen) for k,v in x.items()}
 if isinstance(x,list): return [decode(table,v,seen) for v in x]
 return x

def assert_no_decode_cycle(x,path='$'):
 if isinstance(x,dict):
  assert 'cycle_hashcons_id' not in x,('hashcons cycle in decoded retained data',path,x)
  for k,v in x.items(): assert_no_decode_cycle(v,path+'.'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x): assert_no_decode_cycle(v,f'{path}[{i}]')

# Table projections preserve existing array lengths and indices, nulling every
# declaration row outside the two approved IDs.
projected=copy.deepcopy(raw); P=projected['translated']
for kind,key in GROUPS.items():
 P[key]=[row if isinstance(row,dict) and row.get('def_id') in KEEP[kind] else None for row in D[key]]

def typed_key(row,table_name):
 if not isinstance(row,dict) or not isinstance(row.get('key'),dict) or len(row['key'])!=1:
  raise ValueError(('unrecognized typed-name row',table_name,row))
 kind,ident=next(iter(row['key'].items()))
 if kind not in GROUPS or not isinstance(ident,int):
  raise ValueError(('unrecognized typed-name key',table_name,row.get('key')))
 return kind,ident
for table_name in ('item_names','short_names'):
 P[table_name]=[row for row in D.get(table_name,[]) if typed_key(row,table_name)[1] in KEEP[typed_key(row,table_name)[0]]]
P['ordered_decls']=[{'Type':{'NonRec':9}},{'Fun':{'NonRec':12}}]
# Validate that each root existed at exactly one source table slot before write.
for kind,ident in (('Type',9),('Fun',12)):
 kept=[r for r in P[GROUPS[kind]] if isinstance(r,dict) and r.get('def_id')==ident]
 assert len(kept)==1

# Emit each referenced original hash-cons ID/value on first use. Later uses remain
# Deduplicated references. IDs are never renumbered; fail closed on unknown IDs.
emitted=set()
def rehashcons(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   ident=x['HashConsedValue'][0]
   assert ident in ORIG_HC,('missing original hashcons',ident)
   if ident in emitted: return {'Deduplicated':ident}
   emitted.add(ident); return {'HashConsedValue':[ident,rehashcons(ORIG_HC[ident])]}
  if 'Deduplicated' in x:
   ident=x['Deduplicated']
   assert ident in ORIG_HC,('missing original hashcons',ident)
   if ident in emitted: return {'Deduplicated':ident}
   emitted.add(ident); return {'HashConsedValue':[ident,rehashcons(ORIG_HC[ident])]}
  return {k:rehashcons(v) for k,v in x.items()}
 if isinstance(x,list): return [rehashcons(v) for v in x]
 return x
OUT.write_text(json.dumps(rehashcons(projected),indent=2)+'\n')

# Read-back and full decoded comparison against the authorized projection.
roundtrip=json.loads(OUT.read_text()); assert roundtrip['has_errors'] is False
OUT_HC={}; collect_hashcons(roundtrip,OUT_HC)
def assert_hashcons_resolved(x,path='$'):
 if isinstance(x,dict):
  if 'Deduplicated' in x:
   assert x['Deduplicated'] in OUT_HC,('dangling projected hashcons',path,x['Deduplicated'])
   return
  if 'HashConsedValue' in x:
   assert x['HashConsedValue'][0] in ORIG_HC,('new hashcons id',path,x['HashConsedValue'][0])
  for k,v in x.items(): assert_hashcons_resolved(v,path+'.'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x): assert_hashcons_resolved(v,f'{path}[{i}]')
assert_hashcons_resolved(roundtrip)
assert set(OUT_HC)<=set(ORIG_HC)
assert all(decode(ORIG_HC,ORIG_HC[i])==decode(OUT_HC,OUT_HC[i]) for i in OUT_HC)

original_dec=decode(ORIG_HC,raw); projected_dec=decode(OUT_HC,roundtrip)
# Decode expected projection directly, preserving the intended null slots/maps/order.
expected_dec=decode(ORIG_HC,projected)
assert projected_dec==expected_dec,'projection changed decoded data outside authorized filtering'
# Explicit checks: all declaration slot arrays retain the old lengths; only approved
# IDs survive; the two source rows are identical after complete hash-cons decoding.
counts={}; row_checks=[]
for kind,key in GROUPS.items():
 assert len(roundtrip['translated'][key])==len(D[key])
 present=[]
 for ix,(before,after) in enumerate(zip(D[key],roundtrip['translated'][key])):
  if isinstance(before,dict) and before.get('def_id') in KEEP[kind]:
   assert isinstance(after,dict) and before['def_id']==after['def_id']
   before_dec=decode(ORIG_HC,before); after_dec=decode(OUT_HC,after)
   assert_no_decode_cycle(before_dec,f'{kind}[{ix}].source')
   assert_no_decode_cycle(after_dec,f'{kind}[{ix}].output')
   assert before_dec==after_dec
   present.append(before['def_id'])
   row_checks.append({'kind':kind,'id':before['def_id'],'array_index':ix,'decoded_row_equal':True})
  else:
   assert after is None,('non-retained declaration not null',kind,ix)
 assert set(present)==KEEP[kind]
 counts[kind]=len(present)
assert counts=={'Type':1,'Fun':1,'Global':0,'TraitDecl':0,'TraitImpl':0}
assert roundtrip['translated']['ordered_decls']==[{'Type':{'NonRec':9}},{'Fun':{'NonRec':12}}]

# Precisely account for changed decoded metadata paths.
assert projected_dec['translated']['assoc_item_names']==original_dec['translated']['assoc_item_names']
assert projected_dec['translated']['files']==original_dec['translated']['files']
for key in original_dec['translated']:
 if key in set(GROUPS.values())|{'item_names','short_names','ordered_decls'}: continue
 assert projected_dec['translated'][key]==original_dec['translated'][key],('unapproved translated metadata change',key)
for key in ('charon_version','has_errors'):
 assert projected_dec[key]==original_dec[key]

report={
 'input_sha256':sha(SRC),'output_sha256':sha(OUT),'pinned_reorder_rules_sha256':sha(PINNED),
 'R220_schema_audited_serializer_reference_sha256':sha(R220),'R220_schema_excerpt_sha256':sha(R220_SCHEMA),
 'R298_inventory_sha256':sha(INV),
 'roots':[{'kind':'Type','id':9},{'kind':'Fun','id':12}],
 'ordered_decls':[{'Type':{'NonRec':9}},{'Fun':{'NonRec':12}}],
 'declaration_array_lengths_preserved':{k:len(D[v]) for k,v in GROUPS.items()},
 'retained_declaration_counts':counts,'retained_rows':row_checks,
 'all_decoded_retained_rows_equal':True,'retained_rows_have_no_hashcons_cycles':True,'all_other_decoded_translated_metadata_unchanged':True,
 'only_intended_metadata_projection':{'declaration_rows_except_Type9_Fun12':'null slots, original array lengths kept','item_names':'filtered to retained typed ids','short_names':'filtered to retained typed ids','ordered_decls':'exactly Type NonRec9 then Fun NonRec12'},
 'hashcons':{'original_definition_count':len(ORIG_HC),'output_definition_count':len(OUT_HC),'output_ids_subset_of_original':True,'all_output_deduplicated_refs_resolve':True,'all_output_definition_values_equal_original':True,'dropped_unreferenced_definition_count':len(set(ORIG_HC)-set(OUT_HC)),'dropped_unreferenced_ids':sorted(set(ORIG_HC)-set(OUT_HC))},
 'typed_closure':{'source_inventory_sha256':sha(INV),'declarations':inv['reachable_declarations'],'edges':inv['dependency_edges'],'no_missing':not inv['absent_references_filtered_by_pinned_get_item'],'cycles':inv['cycles'],'unknown_shapes':inv['unknown_reference_shapes']},
 'execution_ast_changes':'none; decoded retained signatures/bodies/rows are byte-structure equivalent to source after hash-cons expansion',
 'translation_or_build_run':False,
 'scope':'Two-row mechanical LLBC projection only; no translation or source-semantics claim.'}
(ROOT/'projection-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'output_sha256':report['output_sha256'],'hashcons_original':len(ORIG_HC),'hashcons_output':len(OUT_HC),'rows':counts,'decoded_equal':report['all_decoded_retained_rows_equal']},indent=2))
