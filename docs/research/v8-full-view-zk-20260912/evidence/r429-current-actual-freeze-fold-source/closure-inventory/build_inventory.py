#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
ROOT=Path.cwd()
OUT=ROOT/'.r21-scratch/r429-actual-freeze-fold/closure-inventory'
SOURCES={
 'R156_LLBC':ROOT/'docs/research/v8-full-view-zk-20260912/evidence/r161-current-base-arithmetic/R156/R156FullFreeze.llbc',
 'R160_LLBC':ROOT/'docs/research/v8-full-view-zk-20260912/evidence/r161-current-base-arithmetic/R160/R160FreezeStd.llbc',
 'R156_Funs':ROOT/'docs/research/v8-full-view-zk-20260912/evidence/r161-current-base-arithmetic/R156/generated/AspisR156FullFreeze/Funs.lean',
 'R156_Types':ROOT/'docs/research/v8-full-view-zk-20260912/evidence/r161-current-base-arithmetic/R156/generated/AspisR156FullFreeze/Types.lean',
 'frozen_Rust':ROOT/'docs/research/v8-full-view-zk-20260912/evidence/freeze-return-continuation-20261002/sources/frozen-relation_callback.rs',
}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def readllbc(key): return json.loads(SOURCES[key].read_text())
def nameparts(meta): return (meta or {}).get('name')
def name_text(parts):
    if not isinstance(parts,list): return str(parts)
    out=[]
    for p in parts:
        if isinstance(p,dict) and 'Ident' in p: out.append(p['Ident'][0])
        elif isinstance(p,dict) and 'Impl' in p: out.append('<impl>')
        elif isinstance(p,dict) and 'Closure' in p: out.append('<closure>')
        else: out.append(str(p))
    return '::'.join(out)
def write_json(name,obj):
    (OUT/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def row_by_id(rows,i):
    r=rows[i]
    if not isinstance(r,dict): raise ValueError(f'null row {i}')
    return r
def direct_callee_ids(ast):
    found=[]
    def walk(x,path='$'):
        if isinstance(x,dict):
            call=x.get('Call')
            if isinstance(call,dict):
                c=call.get('call',{})
                reg=(((c.get('func') or {}).get('Regular') or {}).get('kind') or {}).get('Fun')
                if isinstance(reg,dict) and 'Regular' in reg:
                    found.append({'path':path+'/Call/call/func','fun_id':reg['Regular']})
            for k,v in x.items(): walk(v,path+'/'+k)
        elif isinstance(x,list):
            for i,v in enumerate(x): walk(v,f'{path}/{i}')
    walk(ast)
    return found

def indexed_bundle(which, fun_ids, type_ids):
    d=readllbc(which)['translated']; fs=d['fun_decls']; ts=d['type_decls']
    funcs={str(i):row_by_id(fs,i) for i in fun_ids}
    types={str(i):row_by_id(ts,i) for i in type_ids}
    # Make the actual outer fold call a separate byte-stable JSON artifact.
    outer=funcs['25']['body']['Structured']['body']
    call_stmt=outer['statements'][18]
    exact_call={'function_id':25,'statement_index':18,'statement':call_stmt}
    fold_id=176 if which=='R156_LLBC' else 177
    fold=row_by_id(fs,fold_id)
    data={'input_artifact':str(SOURCES[which].relative_to(ROOT)),'input_sha256':sha(SOURCES[which]),
          'translated_has_errors':readllbc(which).get('has_errors'),
          'outer_freeze_and_closure_function_ids':fun_ids,'captured_closure_type_ids':type_ids,
          'slice_fold_impl_id':fold_id,
          'rows':{'functions':funcs,'types':types,'slice_fold_impl':fold},
          'derived_index':{
             'function_names':{str(i):name_text(row_by_id(fs,i)['item_meta']['name']) for i in fun_ids},
             'type_names':{str(i):name_text(row_by_id(ts,i)['item_meta']['name']) for i in type_ids},
             'outer_call_statement_index':18,
             'outer_call_direct_callees':direct_callee_ids(call_stmt),
             'slice_fold_body_kind':list(fold['body'].keys()) if isinstance(fold.get('body'),dict) else fold.get('body'),
             'captured_state_field_types':{
                str(i): (row_by_id(ts,i).get('kind') or {}).get('Struct',[])
                for i in type_ids
             }
          }}
    prefix='r156' if which=='R156_LLBC' else 'r160'
    write_json(prefix+'-closure-and-fold-rows.json',data)
    write_json(prefix+'-outer-fold-call.json',exact_call)
    write_json(prefix+'-slice-fold-implementation.json',fold)
    return data

r156=indexed_bundle('R156_LLBC',[0,23,24,25,282,283],[18,65])
r160=indexed_bundle('R160_LLBC',[0,23,24,25,283,284],[18,65])
# Hashes and source excerpts are custody/context, not transformed input.
source_hashes={k:{'path':str(p.relative_to(ROOT)),'sha256':sha(p),'size_bytes':p.stat().st_size} for k,p in SOURCES.items()}
write_json('input-source-hashes.json',source_hashes)
# Pin exact generated Lean fold-call block and the source excerpt lines.
fun_lines=SOURCES['R156_Funs'].read_text().splitlines()
(OUT/'r156-generated-fold-call.txt').write_text('\n'.join(fun_lines[1611:1626])+'\n')
rust_lines=SOURCES['frozen_Rust'].read_text().splitlines()
(OUT/'frozen-rust-gamma-closure.txt').write_text('\n'.join(f'{i+1}: {rust_lines[i]}' for i in range(126,145))+'\n')
