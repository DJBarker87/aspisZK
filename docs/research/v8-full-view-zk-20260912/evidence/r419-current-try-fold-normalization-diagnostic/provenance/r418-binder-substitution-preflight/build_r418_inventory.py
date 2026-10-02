#!/usr/bin/env python3
"""Decode only R396 Iterator::try_fold declaration and reference-bearing rows."""
from pathlib import Path
import hashlib, json

ROOT = Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
HERE = ROOT / '.r21-scratch/r418-binder-substitution-preflight'
LLBC = ROOT / 'docs/research/v8-full-view-zk-20260912/evidence/r405-generic-batch-translation-frontier/provenance/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc'
EXPECTED = '399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
raw_bytes = LLBC.read_bytes()
assert hashlib.sha256(raw_bytes).hexdigest() == EXPECTED
raw = json.loads(raw_bytes)
table = {}

def collect(x):
    if isinstance(x, dict):
        if 'HashConsedValue' in x:
            i, v = x['HashConsedValue']
            assert i not in table or table[i] == v
            table[i] = v
            collect(v)
        elif 'Deduplicated' not in x:
            for v in x.values(): collect(v)
    elif isinstance(x, list):
        for v in x: collect(v)

def decode(x, seen=()):
    if isinstance(x, dict):
        if 'HashConsedValue' in x:
            i, v = x['HashConsedValue']
            return {'cycle_hashcons_id': i} if i in seen else decode(v, seen + (i,))
        if 'Deduplicated' in x:
            i = x['Deduplicated']
            return {'cycle_hashcons_id': i} if i in seen else decode(table[i], seen + (i,))
        return {k: decode(v, seen) for k, v in x.items()}
    if isinstance(x, list): return [decode(v, seen) for v in x]
    return x

collect(raw)
root = decode(raw)['translated']
def find_row(rows, ident): return next(r for r in rows if isinstance(r, dict) and r.get('def_id') == ident)
def short_name(name):
    bits=[]
    for part in name or []:
        if 'Ident' in part: bits.append(part['Ident'][0])
        elif 'Impl' in part: bits.append('{impl}')
        else: bits.append('{other}')
    return '::'.join(bits)

trait = find_row(root['trait_decls'], 0)
method = trait['methods'][36]
assert method['skip_binder']['name'] == 'try_fold'
assert short_name(method['skip_binder']['item_meta']['name']) == 'core::iter::traits::iterator::Iterator::try_fold'
target_ids=[58,120,169]
target_funs={i:find_row(root['fun_decls'],i) for i in target_ids}
assert short_name(target_funs[58]['item_meta']['name']) == 'core::iter::traits::iterator::Iterator::try_fold'

# Walk with structural paths to retain method-call generic vectors, distinct from
# the 5-type FunDeclRef generics stored in trait method tables.
trait_method_calls=[]
target_fun_refs=[]
try_output_constraints=[]
def row_name(row): return short_name(row.get('item_meta',{}).get('name'))
for fun in root.get('fun_decls',[]):
    if not isinstance(fun,dict): continue
    for constraint in (fun.get('generics') or {}).get('trait_type_constraints') or []:
        ctext=json.dumps(constraint,separators=(',',':'))
        if '"id":11' in ctext and '"type_id":0' in ctext:
            try_output_constraints.append({'fun_decl_id':fun.get('def_id'),'name':row_name(fun),'span':fun.get('item_meta',{}).get('span'),'type_param_names':[p.get('name') for p in (fun.get('generics') or {}).get('types',[])],'constraint':constraint})
def walk(x, path='$'):
    if isinstance(x, dict):
        kind=x.get('kind')
        if isinstance(kind, dict) and 'Trait' in kind:
            tr=kind['Trait']
            if isinstance(tr, list) and len(tr)==2 and tr[1]==36:
                generics=x.get('generics', {})
                trait_method_calls.append({
                    'path':path,
                    'trait_ref':tr[0],
                    'method_id':tr[1],
                    'generic_args':generics,
                    'arity':{k:len(generics.get(k,[])) for k in ('regions','types','const_generics','trait_refs')},
                })
        if x.get('id') in target_ids and 'generics' in x:
            target_fun_refs.append({'path':path, 'fun_decl_id':x['id'], 'row':x})
        for k,v in x.items(): walk(v, path+'.'+k)
    elif isinstance(x,list):
        for i,v in enumerate(x): walk(v, f'{path}[{i}]')

walk(root)
assert len(target_fun_refs) >= 3, len(target_fun_refs)
assert len(trait_method_calls)==4, len(trait_method_calls)
for ref in target_fun_refs:
    g=ref['row']['generics']
    ref['arity']={k:len(g.get(k,[])) for k in ('regions','types','const_generics','trait_refs')}

# Preserve exact decoded signature/binder rows and reference nodes for review.
payload={
 'classification':'Read-only decoded LLBC census. No LLBC edit, source transformation, compiler run, Lean run, or theorem/source-correspondence decision.',
 'input':{'path':'docs/research/v8-full-view-zk-20260912/evidence/r405-generic-batch-translation-frontier/provenance/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc','sha256':EXPECTED,'has_errors':raw['has_errors'],'hashcons_entries':len(table)},
 'qualified_target':{'fun_decl_id':58,'name':short_name(target_funs[58]['item_meta']['name']),'source_span':target_funs[58]['item_meta']['span'],'related_constraint_functions':[{'fun_decl_id':i,'name':short_name(f['item_meta']['name']),'source_span':f['item_meta']['span']} for i,f in target_funs.items()],'ordered_declaration_occurrences':[x for x in root['ordered_decls'] if x.get('Fun',{}).get('NonRec') in target_ids]},
 'trait_method':{'trait_decl_id':0,'trait_name':short_name(trait['item_meta']['name']),'method_id':36,'method_name':method['skip_binder']['name'],'source_span':method['skip_binder']['item_meta']['span'],'full_binder_and_signature':method},
 'trait_method_impls':[],
 'function_binders_with_Try_Output_constraint':try_output_constraints,
 'direct_fun_decl_refs_id58':target_fun_refs,
 'trait_dispatch_calls_method36':trait_method_calls,
 'limits':['The 3 exact FunDeclRef occurrences are declaration-table refs found by the decoded `id=58` plus `generics` structural predicate. The 4 Trait method-id 36 occurrences are call dispatch refs with their separate method generic arguments. This census does not claim these are the only possible representation locations outside the inspected LLBC schema; all rows are retained for independent inspection.','The function-binder scan matches decoded trait constraints with associated type id 0 and trait declaration id 11 (`Try` in this R396 table); its three matches are preserved verbatim.','No proposed substitution/elimination was applied.']
}
for impl_index,row in enumerate(root['trait_impls']):
    if not isinstance(row,dict): continue
    methods=row.get('methods') or []
    if len(methods)>36 and row.get('impl_trait',{}).get('id')==0:
        impl_ref=methods[36]['skip_binder']
        impl_generics=impl_ref.get('generics',{})
        payload['trait_method_impls'].append({'trait_impl_row_index':impl_index,'trait_impl_def_id':row.get('def_id'),'trait':row.get('impl_trait'),'trait_method_index':36,'method_binder':methods[36].get('params'),'fun_decl_ref':impl_ref,'ref_arity':{k:len(impl_generics.get(k,[])) for k in ('regions','types','const_generics','trait_refs')}})
payload['direct_fun_decl_refs_id58']=target_fun_refs
(HERE/'decoded-reference-census.json').write_text(json.dumps(payload,indent=2)+'\n')

manifest=json.loads((HERE/'source-manifest.json').read_text())
manifest['r396_decoded_reference_census']={'path':'decoded-reference-census.json','sha256':hashlib.sha256((HERE/'decoded-reference-census.json').read_bytes()).hexdigest(),'target_input_sha256':EXPECTED}
(HERE/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'input_sha256':EXPECTED,'hashcons_entries':len(table),'target_fun_decl_refs':len(target_fun_refs),'trait_method_dispatches':len(trait_method_calls),'trait_impl_method_refs':len(payload['trait_method_impls']),'function_binders_with_Try_Output_constraint':[x['fun_decl_id'] for x in try_output_constraints],'census':str(HERE/'decoded-reference-census.json')},indent=2))
