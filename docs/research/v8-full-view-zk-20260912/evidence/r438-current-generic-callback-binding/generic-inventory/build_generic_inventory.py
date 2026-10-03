#!/usr/bin/env python3
"""Read-only extraction of captured generic FnMut/call/fold binding rows."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
CAP=HERE.parent/'root-launch-a/saved-output/R438GenericClosureDispatch.llbc'
# Resolve actual capture regardless of inventory sibling layout.
if not CAP.exists():
    CAP=Path(__file__).resolve().parents[4]/'.r21-scratch/r438-fnmut-source-selection/root-launch-a/saved-output/R438GenericClosureDispatch.llbc'
raw=json.loads(CAP.read_text()); t=raw['translated']
def walk(v,path=()):
    if isinstance(v,dict):
        yield path,v
        for k,x in v.items(): yield from walk(x,path+(k,))
    elif isinstance(v,list):
        for i,x in enumerate(v): yield from walk(x,path+(i,))
hc={}
for _,n in walk(t):
    x=n.get('HashConsedValue') if isinstance(n,dict) else None
    if isinstance(x,list) and len(x)==2:
        if x[0] in hc and hc[x[0]]!=x[1]: raise ValueError(f'inconsistent hashcons {x[0]}')
        hc[x[0]]=x[1]
def dec(x):
    if isinstance(x,dict):
        if set(x)=={'HashConsedValue'}: return dec(x['HashConsedValue'][1])
        if set(x)=={'Deduplicated'}: return dec(hc[x['Deduplicated']])
        return {k:dec(v) for k,v in x.items()}
    if isinstance(x,list): return [dec(v) for v in x]
    return x
def byid(rows,i):
    return next(x for x in rows if x is not None and x['def_id']==i)
def call_nodes(fid):
    f=byid(t['fun_decls'],fid); out=[]
    for path,n in walk(f.get('body',{})):
        if 'Call' in n:
            c=n['Call']['call']; reg=c['func'].get('Regular',{})
            out.append({'path':list(path),'callee_kind':reg.get('kind'),'generics_raw':reg.get('generics'),'args_raw':c.get('args'),'dest_raw':c.get('dest')})
    return out
fids=[24,25,176,283,284]
functions=[]
for i in fids:
    f=byid(t['fun_decls'],i)
    functions.append({'def_id':i,'item_meta':f['item_meta'],'source_descriptor_raw':f['src'],'generics_raw':f['generics'],'generics_resolved':dec(f['generics']),'signature_raw':f['signature'],'signature_resolved':dec(f['signature']),'body_kind':list(f['body'].keys()),'direct_calls':call_nodes(i)})
impls=[]
for i in [46,47]:
    x=t['trait_impls'][i]
    impls.append({'def_id':i,'item_meta':x['item_meta'],'impl_trait_raw':x['impl_trait'],'impl_trait_resolved':dec(x['impl_trait']),'generics_raw':x['generics'],'methods_raw':x['methods'],'types_raw':x['types'],'consts_raw':x['consts']})
traits=[]
for i in [0,8,9]:
    x=t['trait_decls'][i]
    traits.append({'def_id':i,'item_meta':x['item_meta'],'generics_raw':x['generics'],'methods_raw':x['methods'],'types_raw':x['types'],'associated_item_names':t['assoc_item_names'][i]})
# Include exact selected row for closure environment type; `def_id` identifies the declaration independent of row position.
types=[]
for i in [65]:
    x=byid(t['type_decls'],i)
    types.append({'def_id':i,'item_meta':x['item_meta'],'generics_raw':x['generics'],'kind_raw':x.get('kind'),'body_kind':list(x.get('body',{}).keys()) if isinstance(x.get('body'),dict) else None,'body_raw':x.get('body')})
byfun={f['def_id']:f for f in functions}
byimpl={i['def_id']:i for i in impls}
bytrait={i['def_id']:i for i in traits}
fun24_to25=[c for c in byfun[24]['direct_calls'] if c['callee_kind']=={'Fun':{'Regular':25}}]
fun25_to176=[c for c in byfun[25]['direct_calls'] if c['callee_kind']=={'Fun':{'Regular':176}}]
fold_clause_calls=[c for c in byfun[176]['direct_calls'] if isinstance(c['callee_kind'],dict) and 'Trait' in c['callee_kind']]
assert len(fun24_to25)==1 and len(fun25_to176)==1
assert len(fold_clause_calls)==1
trait_payload=fold_clause_calls[0]['callee_kind']['Trait']
fold_ref=dec(trait_payload[0])
assert trait_payload[1]==0 and fold_ref.get('kind',{}).get('Clause')=={'Free':0}
assert fold_ref.get('trait_decl_ref',{}).get('skip_binder',{}).get('id')==9
assert byfun[176]['source_descriptor_raw']['TraitImpl']['impl_ref']['id']==31
assert byfun[176]['source_descriptor_raw']['TraitImpl']['trait_ref']['id']==5
assert byfun[176]['source_descriptor_raw']['TraitImpl']['item_id']=={'Method':38}
assert byfun[24]['source_descriptor_raw']['TraitImpl']['trait_ref']['id']==9 and byfun[24]['source_descriptor_raw']['TraitImpl']['item_id']=={'Method':0}
assert byfun[25]['source_descriptor_raw']['TraitImpl']['trait_ref']['id']==8 and byfun[25]['source_descriptor_raw']['TraitImpl']['item_id']=={'Method':0}
instantiated_fold_call=fun25_to176[0]
instantiated_trait=dec(instantiated_fold_call['generics_raw']['trait_refs'][0])
assert instantiated_trait.get('kind',{}).get('TraitImpl',{}).get('id')==47
assert instantiated_trait.get('trait_decl_ref',{}).get('skip_binder',{}).get('id')==9
assert instantiated_trait.get('kind',{}).get('TraitImpl',{}).get('generics',{}).get('regions')==[{'Body':21},{'Body':22},{'Body':32}]
assert instantiated_fold_call['generics_raw']['regions']==[{'Body':18}]
closure_arg_type=dec(instantiated_fold_call['generics_raw']['types'][2])
assert closure_arg_type.get('Adt',{}).get('id')=={'Adt':65}
assert closure_arg_type.get('Adt',{}).get('generics',{}).get('regions')==[{'Body':21},{'Body':22}]
assert byimpl[47]['methods_raw'][0]['skip_binder']['id']==284
assert byimpl[47]['methods_raw'][0]['kind']=={'TraitMethod':[9,0]}
assert byimpl[47]['methods_raw'][0]['params']['regions']==[{'index':0,'mutability':'Unknown','name':None}]
assert byimpl[47]['impl_trait_raw']['id']==9
assert byimpl[46]['methods_raw'][0]['skip_binder']['id']==283
assert byimpl[46]['methods_raw'][0]['kind']=={'TraitMethod':[0,0]}
assert byimpl[46]['impl_trait_raw']['id']==0
for i in [0,8,9]: assert len(bytrait[i]['methods_raw'])==1
for fid,iid,tid,method in [(284,47,9,0),(283,46,0,0)]:
    src=byfun[fid]['source_descriptor_raw']['TraitImpl']
    assert src['impl_ref']['id']==iid and src['trait_ref']['id']==tid and src['item_id']=={'Method':method} and src['reuses_default'] is False
assert byfun[284]['item_meta']['span']==byfun[283]['item_meta']['span']
assert byfun[284]['item_meta']['name'][-1]=={'Ident':['call_mut',0]}
assert byfun[283]['item_meta']['name'][-1]=={'Ident':['call_once',0]}
checks=[
 {'check':'Fun24-call_mut-shim-calls-Fun25','pass':True,'fun24_call_path':fun24_to25[0]['path'],'source':byfun[24]['source_descriptor_raw']},
 {'check':'Fun25-fold-call-is-Fun176-and-carries-Impl47-FnMut','pass':True,'call_path':fun25_to176[0]['path'],'callee':fun25_to176[0]['callee_kind'],'generics_raw':fun25_to176[0]['generics_raw'],'decoded_trait_impl_id':47,'decoded_trait_decl_id':9,'closure_type_decoded':closure_arg_type,'trait_impl_regions':[{'Body':21},{'Body':22},{'Body':32}], 'fold_region_argument':[{'Body':18}]},
 {'check':'Fun176-is-iterator-fold-and-callback-is-ClauseFree0-FnMut9-slot0','pass':True,'fold_source':byfun[176]['source_descriptor_raw'],'callback_path':fold_clause_calls[0]['path'],'callback_kind':fold_clause_calls[0]['callee_kind'],'callback_generics':fold_clause_calls[0]['generics_raw']},
 {'check':'FnMut-impl47-method0-binds-Fun284','pass':True,'source':byfun[284]['source_descriptor_raw'],'method_binding':byimpl[47]['methods_raw'][0]},
 {'check':'FnOnce-impl46-method0-binds-Fun283','pass':True,'source':byfun[283]['source_descriptor_raw'],'method_binding':byimpl[46]['methods_raw'][0]},
 {'check':'trait-declaration-method-slots-present','pass':True,'trait_ids':[0,8,9]}
]
result={'capture_path':str(CAP),'capture_sha256':hashlib.sha256(CAP.read_bytes()).hexdigest(),'charon_version':raw.get('charon_version'),'has_errors':raw.get('has_errors'),'mechanical_checks':checks,'functions':functions,'types':types,'trait_declarations':traits,'trait_implementations':impls,'interpretation_boundary':'Literal generic LLBC rows, function-pointer references, signatures, binders and source spans only. Does not infer that captured method references execute or establish Rust dispatch/source correspondence.'}
(HERE/'generic-binding-inventory.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'capture_sha256':result['capture_sha256'],'functions':[(x['def_id'],x['item_meta']['name']) for x in functions],'trait_impl_method_counts':[(x['def_id'],len(x['methods_raw'])) for x in impls]},indent=2))
