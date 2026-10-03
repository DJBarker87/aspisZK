#!/usr/bin/env python3
"""Mechanical inventory of function-pointer/closure-call LLBC references; no semantic claim."""
import hashlib, json
from pathlib import Path
ROOT=Path.cwd()
SRC=ROOT/'.r21-scratch/r437-pointer-source-boundary/root-launch-a/saved-output/R437PointerWrapperLayout.llbc'
PIN='bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c'
OUT=ROOT/'.r21-scratch/r440-mono-closure-binding/actual-source-preflight/inventory'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SRC)==PIN
raw=json.loads(SRC.read_text()); assert raw['has_errors'] is False
tr=raw['translated']
defs={}
def collect(x):
    if isinstance(x,dict):
        h=x.get('HashConsedValue')
        if isinstance(h,list) and len(h)==2:
            i,v=h
            if i in defs and defs[i]!=v: raise ValueError(f'hashcons collision {i}')
            defs[i]=v
        for v in x.values():collect(v)
    elif isinstance(x,list):
        for v in x:collect(v)
collect(tr)
def expand(x,stack=()):
    if isinstance(x,dict):
        if set(x)=={'HashConsedValue'}:
            i=x['HashConsedValue'][0]
            if i in stack:raise ValueError(f'hashcons cycle {i}')
            return expand(defs[i],stack+(i,))
        if set(x)=={'Deduplicated'}:
            i=x['Deduplicated']
            if i in stack:raise ValueError(f'dedup cycle {i}')
            return expand(defs[i],stack+(i,))
        return {k:expand(v,stack) for k,v in x.items()}
    if isinstance(x,list):return [expand(v,stack) for v in x]
    return x
ex=expand(tr)
# Every reference is preserved exactly as it appears after resolving only hashcons wrappers.
fnptr=[]; fndef=[]; traitfnptr=[]; calls=[]
def walk(x,path=()):
    if isinstance(x,dict):
        for k,v in x.items():
            if k=='FnPtr': fnptr.append({'path':list(path+[k]),'value':v})
            if k=='FnDef': fndef.append({'path':list(path+[k]),'value':v})
            if k=='TraitFnPtr': traitfnptr.append({'path':list(path+[k]),'value':v})
            if k=='Call' and isinstance(v,dict) and isinstance(v.get('call'),dict):
                calls.append({'path':list(path+[k]),'call':v['call']})
            walk(v,path+[k])
    elif isinstance(x,list):
        for i,v in enumerate(x):walk(v,path+[i])
# Restrict expression scans to function bodies and global/constant rows; also scan declaration
# signatures/types separately so type-level FnPtr entries are not mislabeled as expressions.
for table in ('fun_decls','global_decls'):
    for i,row in enumerate(ex[table]):
        if row is not None:
            if table=='fun_decls':
                walk(row.get('body'),[table,i,'body'])
            else:
                walk(row,[table,i])
expr_fnptr,expr_fndef,expr_traitfnptr=fnptr,fndef,traitfnptr
# Complete type/signature inventory over all declaration tables, labelled separately.
type_occ=[]
def scan_types(x,path=()):
    if isinstance(x,dict):
        for k,v in x.items():
            if k in ('FnPtr','FnDef','TraitFnPtr'):
                type_occ.append({'kind':k,'path':list(path+[k]),'value':v})
            scan_types(v,path+[k])
    elif isinstance(x,list):
        for i,v in enumerate(x):scan_types(v,path+[i])
for table in ('type_decls','fun_decls','global_decls','trait_decls','trait_impls'):
    for i,row in enumerate(ex[table]):
        if row is not None:scan_types(row,[table,i])
# Trait paths from stable declaration rows.
def name_parts(row):
    parts=[]
    for p in row.get('item_meta',{}).get('name') or []:
        if isinstance(p,dict) and 'Ident' in p:parts.append(p['Ident'][0])
        elif isinstance(p,dict) and 'Impl' in p:parts.append('<impl>')
        elif isinstance(p,dict) and 'Instantiated' in p:parts.append('<instantiated>')
    return parts
trait_names={i:name_parts(r) for i,r in enumerate(ex['trait_decls']) if r is not None}
fn_trait_ids={i for i,n in trait_names.items() if n and n[-1] in ('Fn','FnMut','FnOnce')}
# Record all Fn/FnMut/FnOnce trait-call expression references, preserving full operands,
# destination/unwind, pointer kind, trait/impl args, and method args.
fn_trait_calls=[]
for callrow in calls:
    c=callrow['call']; regular=c.get('func',{}).get('Regular')
    if not isinstance(regular,dict):continue
    kind=regular.get('kind',{})
    if not isinstance(kind,dict) or 'Trait' not in kind:continue
    tr,slot=kind['Trait']
    trait_id=tr.get('trait_decl_ref',{}).get('skip_binder',{}).get('id')
    tk=tr.get('kind',{})
    impl_ref=tk.get('TraitImpl') if isinstance(tk,dict) else None
    if trait_id in fn_trait_ids:
        impl_id=impl_ref.get('id') if isinstance(impl_ref,dict) else None
        fn_trait_calls.append({
            'path':callrow['path'],'owner_fun_id':callrow['path'][1] if len(callrow['path'])>1 else None,
            'trait_id':trait_id,'trait_name':'::'.join(trait_names[trait_id]),'method_slot':slot,
            'impl_id':impl_id,'impl_generics':impl_ref.get('generics') if isinstance(impl_ref,dict) else None,
            'method_generics':regular.get('generics'),'args':c.get('args'),'destination':c.get('destination'),'unwind':c.get('unwind'),
        })
# Source ownership gives a serialized candidate Fun id only when (impl id, method slot) is unique.
owners={}
for f in ex['fun_decls']:
    if not isinstance(f,dict):continue
    src=f.get('src')
    if not isinstance(src,dict) or 'TraitImpl' not in src:continue
    s=src['TraitImpl']; ir=s.get('impl_ref',{}); item=s.get('item_id',{})
    if isinstance(item,dict) and 'Method' in item and isinstance(ir,dict):
        owners.setdefault((ir.get('id'),item['Method']),[]).append(f.get('def_id'))
for r in fn_trait_calls:
    matches=owners.get((r['impl_id'],r['method_slot']),[])
    r['source_owned_method_fun_ids']=matches
    r['source_owner_match_status']='unique' if len(matches)==1 else ('none' if not matches else 'ambiguous')
# A closure impl can have a generated `Impl` path with no `closure` segment. Identify it
# from the exact self-type ADT's native declaration name; retain the full trait args and map.
type_names={i:name_parts(r) for i,r in enumerate(ex['type_decls']) if isinstance(r,dict)}
closure_impls=[]
for i,row in enumerate(ex['trait_impls']):
    if not isinstance(row,dict):continue
    it=row.get('impl_trait',{}); tid=it.get('id'); nm=name_parts(row)
    type_args=(it.get('generics') or {}).get('types') or []
    self_ty=type_args[0] if type_args else None
    adt_ref=self_ty.get('Adt',{}).get('id') if isinstance(self_ty,dict) else None
    adt_id=adt_ref.get('Adt') if isinstance(adt_ref,dict) else None
    self_name=type_names.get(adt_id,[])
    is_closure_self=bool(self_name and 'closure' in self_name)
    if tid in fn_trait_ids and is_closure_self:
        closure_impls.append({'impl_id':i,'trait_id':tid,'trait_name':'::'.join(trait_names[tid]),
            'item_name_parts':nm,'self_type_adt_id':adt_id,'self_type_name_parts':self_name,
            'self_type_exact':self_ty,'trait_ref_generics':it.get('generics'),
            'methods_exact':row.get('methods'),'item_meta':row.get('item_meta')})
# Source-owned Fn-family method declarations and exact ownership metadata.
closure_methods=[]
for f in ex['fun_decls']:
    if not isinstance(f,dict):continue
    src=f.get('src')
    if not isinstance(src,dict) or 'TraitImpl' not in src:continue
    s=src['TraitImpl']; tid=s.get('trait_ref',{}).get('id')
    if tid in fn_trait_ids:
        closure_methods.append({'fun_id':f.get('def_id'),'trait_id':tid,'trait_name':'::'.join(trait_names[tid]),
            'item_name_parts':name_parts(f),'src_exact':src,'signature_exact':f.get('signature'),
            'matching_trait_impl_row':s.get('impl_ref',{}).get('id')})
# Summarize each FnPtr signature by exact value digest without collapsing its occurrence paths.
from collections import Counter
fnptr_sig_counts=Counter(json.dumps(r['value'],sort_keys=True,separators=(',',':')) for r in type_occ if r['kind']=='FnPtr')
report={
 'status':'read-only LLBC inventory; no source-to-model or execution-semantics conclusion',
 'source':{'path':str(SRC.relative_to(ROOT)),'sha256':sha(SRC),'bytes':SRC.stat().st_size,'has_errors':raw['has_errors'],'charon_version':raw.get('charon_version'),'capture_revision':'77857d6028d1b4016949aa14b19c17282e2cec0c'},
 'hashcons':{'entry_count':len(defs),'expansion':'only HashConsedValue/Deduplicated wrappers expanded; no values/regions/generic args erased'},
 'declaration_counts':{k:len(ex[k]) for k in ('type_decls','fun_decls','global_decls','trait_decls','trait_impls')},
 'function_pointer_inventory':{'expression_body_and_global':{'FnPtr_occurrences':len(expr_fnptr),'TraitFnPtr_occurrences':len(expr_traitfnptr),'FnDef_occurrences':len(expr_fndef),'FnPtr':expr_fnptr,'TraitFnPtr':expr_traitfnptr,'FnDef':expr_fndef},
   'all_declaration_type_occurrences':{'counts':dict(__import__('collections').Counter(o['kind'] for o in type_occ)),'entries':type_occ,'FnPtr_signature_digest_counts':dict(fnptr_sig_counts)},
   'note':'TraitFnPtr is not a literal tag in this decoded LLBC; trait method invocation is represented under Call.func.Regular.kind.Trait.'},
 'fn_family':{'trait_ids':{str(i):trait_names[i] for i in sorted(fn_trait_ids)},'trait_fn_method_maps':{str(i):ex['trait_decls'][i].get('methods') for i in sorted(fn_trait_ids)},
   'closure_trait_impl_rows':closure_impls,'source_owned_fn_family_method_functions':closure_methods,'trait_call_sites':fn_trait_calls,'closure_trait_call_sites':[r for r in fn_trait_calls if r['impl_id'] in {x['impl_id'] for x in closure_impls}]},
}
out=OUT/'fn-pointer-closure-inventory.json';out.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps({'out':str(out),'out_sha256':sha(out),'raw_input_sha256':sha(SRC),'fnptr_expr':len(expr_fnptr),'fndef_expr':len(expr_fndef),'traitfnptr_expr':len(expr_traitfnptr),'fnptr_types':sum(o['kind']=='FnPtr' for o in type_occ),'fndef_types':sum(o['kind']=='FnDef' for o in type_occ),'traitfnptr_types':sum(o['kind']=='TraitFnPtr' for o in type_occ),'fn_trait_calls':len(fn_trait_calls),'closure_impls':len(closure_impls),'owned_methods':len(closure_methods)},indent=2))
