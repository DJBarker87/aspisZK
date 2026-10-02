#!/usr/bin/env python3
"""Read-only closure/type/SSA facts from the saved R327 LLBC and R357 artifacts."""
from pathlib import Path
import hashlib, json
ROOT = Path(__file__).resolve().parents[2]
R327 = ROOT / '.r21-scratch/r327-private-batch-source-try-fold/R327PrivateBatchSourceTryFold.llbc'
R357 = ROOT / '.r21-scratch/r357-batch-zero-predicate-raw'
OUT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
raw = json.loads(R327.read_text()); tr = raw['translated']
# Resolve Charon's hash-cons table without altering the serialized input.
hc = {}
def collect(x):
    if isinstance(x, dict):
        if 'HashConsedValue' in x:
            i, v = x['HashConsedValue']; hc[i] = v; collect(v)
        elif 'Deduplicated' not in x:
            for v in x.values(): collect(v)
    elif isinstance(x, list):
        for v in x: collect(v)
collect(raw)
def dec(x):
    if isinstance(x, dict):
        if 'HashConsedValue' in x: return dec(x['HashConsedValue'][1])
        if 'Deduplicated' in x: return dec(hc[x['Deduplicated']])
        return {k: dec(v) for k,v in x.items()}
    if isinstance(x, list): return [dec(v) for v in x]
    return x
def byid(table, i): return next(x for x in tr[table] if isinstance(x,dict) and x.get('def_id') == i)
def name(r):
    parts=[]
    for x in r.get('item_meta',{}).get('name') or []:
        if 'Ident' in x: parts.append(x['Ident'][0])
        elif 'Impl' in x: parts.append('{impl-trait#'+str(x['Impl'].get('Trait'))+'}')
    return '::'.join(parts)
def source_span(r): return r.get('item_meta',{}).get('span')

t7, t15 = byid('type_decls',7), byid('type_decls',15)
impl1, impl14, impl24 = byid('trait_impls',1), byid('trait_impls',14), byid('trait_impls',24)
t16 = byid('type_decls',16)
f35, f36, f47 = byid('fun_decls',35), byid('fun_decls',36), byid('fun_decls',47)
b36_structured = dec(f36['body'])['Structured']
b36 = b36_structured['body']
loop = b36['statements'][4]['kind']['Loop']
assign_closure_ref = loop['statements'][8]
call_mut = loop['statements'][14]
assert assign_closure_ref['id'] == 5446 and call_mut['id'] == 5463
assert call_mut['kind']['Call']['call']['func']['Regular']['kind']['Fun'] == {'Regular':47}
assert call_mut['kind']['Call']['call']['args'][0]['Move']['kind']['Local'] == 8
assert assign_closure_ref['kind']['Assign'][0]['kind']['Local'] == 8
assert assign_closure_ref['kind']['Assign'][1]['Ref']['place']['kind']['Local'] == 3
assert b36_structured['locals']['locals'][3]['name'] == 'f'
assert dec(f47.get('body')) == 'Opaque'

r = {
 'status':'read-only LLBC representation inventory; no layout or dispatch inference',
 'inputs': {
   'R327_LLBC': {'path':str(R327.relative_to(ROOT)), 'sha256':sha(R327), 'has_errors':raw.get('has_errors')},
   'R357_raw_target': {'path':str((R357/'AspisR357BatchZeroPredicateRaw.lean').relative_to(ROOT)), 'sha256':sha(R357/'AspisR357BatchZeroPredicateRaw.lean')},
   'R357_source_provenance': {'path':str((R357/'provenance/generator-report.json').relative_to(ROOT)), 'sha256':sha(R357/'provenance/generator-report.json')},
 },
 'closure_types': [
   {'def_id':7,'name':name(t7),'source_span':source_span(t7),'source_kind':'Closure','closure_kind':'FnMut',
    'generic_regions_types_const_generics':{'regions':0,'types':0,'const_generics':0},
    'struct_fields':[], 'source_closure_signature':dec(t7['src'])['Closure']['info']['signature'],
    'serialized_concrete_abi_layout':'not present in this LLBC type row'},
   {'def_id':15,'name':name(t15),'source_span':source_span(t15),'source_kind':'Closure','closure_kind':'FnMut',
    'generic_regions_types_const_generics':{'regions':0,'types':0,'const_generics':0},
    'struct_fields':[{'field_index':0,'name':None,'type':{'Adt':7,'name':name(t7)},'field_span':t15['kind']['Struct'][0]['span']}],
    'source_closure_signature':dec(t15['src'])['Closure']['info']['signature'],
    'serialized_concrete_abi_layout':'not present in this LLBC type row'}
 ],
 'id_disambiguation': {'type_decl_16_name':name(t16),'note':'TypeDecl 16 is M31, not one of the two closure types identified here.'},
 'trait_impl_and_methods': {
   'TraitImpl1': {'name':name(impl1),'span':source_span(impl1),'impl_trait':dec(impl1['impl_trait']),'generic_regions':len(impl1['generics']['regions']),
                  'relation':'Fun35 body contains a Trait call whose TraitImpl target is id 1; this row is the actual batch::closure FnMut impl in the LLBC graph.'},
   'TraitImpl14': {'name':name(impl14),'span':source_span(impl14),'source':'core::iter::traits::iterator::Iterator::any::check closure implementation',
                   'impl_trait':dec(impl14['impl_trait']),'generic_regions':len(impl14['generics']['regions']),'methods':dec(impl14['methods'])},
   'Fun35': {'name':name(f35),'span':source_span(f35),'source':dec(f35.get('src')),
             'body_status':'structured','body_observed_operation':'projects field 0 of the Type15 closure (Type7) and calls TraitImpl1 (the batch::closure FnMut implementation) with a mutable receiver reference and tupled argument; the call is trait-implementation-dispatched in LLBC, not reduced here'},
   'TraitImpl24': {'name':name(impl24),'span':source_span(impl24),'impl_trait':dec(impl24['impl_trait']),
                   'generic_regions':len(impl24['generics']['regions']),'generic_types':len(impl24['generics']['types']),
                   'methods':dec(impl24['methods']),'vtable':dec(impl24['vtable'])},
   'Fun47': {'name':name(f47),'span':source_span(f47),'source':dec(f47.get('src')),'body_status':'Opaque',
             'signature':dec(f47['signature'])},
 },
 'Fun36_closure_parameter_SSA': {
   'name':name(f36),'span':source_span(f36),'source':dec(f36.get('src')),
   'signature':dec(f36['signature']),
   'parameter_local':{'id':3,'name':'f','type':dec(b36_structured['locals']['locals'][3]['ty'])},
   'direct_closure_place_uses':[
      {'statement_id':5446,'loop_statement_index':8,'operation':'mutable Ref constructed with place Local(3)',
       'destination_local':8,'destination_type':dec(assign_closure_ref['kind']['Assign'][0]['ty'])}
   ],
   'call':{'statement_id':5463,'loop_statement_index':14,'target_fun_id':47,'target_name':name(f47),
           'target_body_status':'Opaque','argument0':'Move Local(8), the mutable reference created from f','argument1':'Move Local(9), tuple containing accumulator and shared reference to current item',
           'destination_local':7},
   'direct_parameter_assignments':'none in function body; its only direct place use is the mutable borrow at statement 5446, subsequently moved to call target 47 at statement 5463',
 },
 'R357_actual_source_predicate': {
   'source_file':'frozen r110_norm.rs represented in R327 file id 0',
   'source_span':'line 62, columns 61–75 (closure expression)',
   'enclosing_predicate_span':'line 62: `xs.iter().chain(ys).any(|x|*x==B::ZERO)`',
   'R357_generated_environment':'batch.closure is defined as Unit in provenance/unit_closure_type.excerpt.lean; raw generator report identifies a mechanical copy from the saved Types input',
   'R357_call_mut':'source-shaped function takes c : batch.closure and tupled_args : B; compares tupled_args to B.ZERO and returns (bool,c)',
   'scope_note':'These are declaration/source-shape facts. They do not identify a runtime closure layout or prove dispatch/equivalence.'
 },
 'limits':['No concrete ABI/layout data is serialized for TypeDecl 7 or 15 in the inspected LLBC rows.',
           'No inference that an empty struct or Unit is zero-sized, singleton, optimized away, or interchangeable at runtime.',
           'Trait implementation rows and source spans do not prove dynamic/concrete dispatch beyond the explicit LLBC call edge Fun36 -> Fun47.',
           'No claim of full Rust source correspondence, lifetime erasure, or proof closure.']
}
(OUT/'inventory.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'output':str((OUT/'inventory.json').relative_to(ROOT)),'sha256':sha(OUT/'inventory.json'),'input_sha256':sha(R327),'types':[{'id':x['def_id'],'name':x['name'],'field_count':len(x['struct_fields'])} for x in r['closure_types']],'call_target':r['Fun36_closure_parameter_SSA']['call']['target_name'] if 'Fun36_closure_parameter_SSA' in r else r['Fun36_closure_parameter_SSA']['call']['target_name']},indent=2))
