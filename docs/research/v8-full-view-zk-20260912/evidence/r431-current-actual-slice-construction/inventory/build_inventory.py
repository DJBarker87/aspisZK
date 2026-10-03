#!/usr/bin/env python3
"""Build a read-only index of the R431 constructor capture's exact LLBC rows."""
import hashlib, json
from pathlib import Path
ROOT = Path.cwd()
OUT = ROOT / '.r21-scratch/r431-actual-slice-construction/inventory'
INPUT = ROOT / '.r21-scratch/r431-actual-slice-construction/root-launch-a/saved-output/R431ActualSliceConstruction.llbc'
R429 = ROOT / '.r21-scratch/r429-actual-freeze-fold/root-launch-c/saved-output/R429ActualFreezeFold.llbc'
STDLIB = ROOT / '.r21-scratch/r431-actual-slice-construction/stdlib-contracts'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
def name_text(name):
    if not isinstance(name, list): return str(name)
    out=[]
    for p in name:
        if isinstance(p,dict) and 'Ident' in p: out.append(p['Ident'][0])
        elif isinstance(p,dict) and 'Impl' in p: out.append('<impl>')
        elif isinstance(p,dict) and 'Closure' in p: out.append('<closure>')
        elif isinstance(p,dict) and 'Instantiated' in p: continue
        else: out.append(str(p))
    return '::'.join(out)
def writej(name,obj): (OUT/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def direct_ids(obj):
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
    walk(obj); return found
def row(rows,i):
    r=rows[i]
    if not isinstance(r,dict): raise ValueError(f'row {i} missing/non-object')
    return r

def bundle(path, filename, function_ids, type_ids, global_ids, trait_ids=None, impl_ids=None):
    raw=read(path); d=raw['translated']
    fs=d['fun_decls']; ts=d['type_decls']; gs=d['global_decls']
    selected_f={str(i):row(fs,i) for i in function_ids}
    selected_t={str(i):row(ts,i) for i in type_ids}
    selected_g={str(i):row(gs,i) for i in global_ids}
    selected_tr={str(i):row(d['trait_decls'],i) for i in (trait_ids or [])}
    selected_impl={str(i):row(d['trait_impls'],i) for i in (impl_ids or [])}
    data={
      'input':str(path.relative_to(ROOT)), 'input_sha256':sha(path),
      'has_errors':raw.get('has_errors'), 'crate_name':d.get('crate_name'),
      'selected_function_ids':function_ids,'selected_type_ids':type_ids,
      'selected_global_ids':global_ids,'selected_trait_ids':trait_ids or [],
      'selected_trait_impl_ids':impl_ids or [],
      'rows':{'functions':selected_f,'types':selected_t,'globals':selected_g,
              'traits':selected_tr,'trait_impls':selected_impl},
      'derived':{
        'function_names':{str(i):name_text(row(fs,i)['item_meta']['name']) for i in function_ids},
        'type_names':{str(i):name_text(row(ts,i)['item_meta']['name']) for i in type_ids},
        'global_names':{str(i):name_text(row(gs,i)['item_meta']['name']) for i in global_ids},
        'direct_function_references':{str(i):direct_ids(row(fs,i).get('body')) for i in function_ids},
        'function_body_forms':{str(i):list(row(fs,i)['body']) if isinstance(row(fs,i).get('body'),dict) else row(fs,i).get('body') for i in function_ids},
      }
    }
    writej(filename,data)
    return data

raw=read(INPUT); d=raw['translated']
assert raw.get('has_errors') is False
# IDs are native ordered-declaration row indices in this exact capture.
fun_ids=[0,27,28,29,43,70,76,86,111,112,114,115,116,144,145]
type_ids=[2,26,42,50,58,59]
global_ids=[14,31,32]
# Function 43 is the selected slice method; 86 is its emitted Iter::new body.
selected=bundle(INPUT,'r431-selected-path-rows.json',fun_ids,type_ids,global_ids,trait_ids=[3],impl_ids=[34,35])
# Complete root call nodes, preserved byte-structurally in JSON.
root=row(d['fun_decls'],29); root_body=root['body']['Structured']['body']
for ix in (8,18):
    st=root_body['statements'][ix]
    writej(f'r431-freeze-call-stmt-{ix}.json',{'function_id':29,'statement_index':ix,'statement':st})
# Preserve constructor and fold control-flow statements explicitly too.
for fid, indices, label in [(86,list(range(len(d['fun_decls'][86]['body']['Structured']['body']['statements']))),'iter-new'),
                              (70,[9,10],'fold-control-flow')]:
    body=d['fun_decls'][fid]['body']['Structured']['body']
    writej(f'r431-{label}-statements.json',{'function_id':fid,'source_name':name_text(d['fun_decls'][fid]['item_meta']['name']),
        'statement_indices':indices,'statements':[body['statements'][i] for i in indices]})
# Keep exact source line excerpts from the already pinned source snapshot.
source_map=[('slice/mod.rs','source/core/slice/mod.rs',1021,1043),
            ('slice-iter.rs','source/core/slice/iter.rs',67,104),
            ('slice-iter-macros.rs','source/core/slice/iter/macros.rs',1,61),
            ('slice-iter-fold-macro.rs','source/core/slice/iter/macros.rs',259,289)]
for outname, rel, start, end in source_map:
    p=STDLIB/rel; lines=p.read_text().splitlines()
    (OUT/(outname.replace('/','_')+'-source.txt')).write_text('\n'.join(f'{i+1}: {lines[i]}' for i in range(start-1,end))+'\n')
# Compact, derived call/operation census; complete source AST rows remain in JSON above.
def kind_counts(obj):
    wanted={'Call','Switch','Aggregate','UnaryOp','BinaryOp','Transmute','RawPtr','NullaryOp','Assert','Loop','Break','Continue','Ref','Drop','Return','UnwindResume'}
    from collections import Counter
    c=Counter()
    def walk(x):
        if isinstance(x,dict):
            for k,v in x.items():
                if k in wanted: c[k]+=1
                walk(v)
        elif isinstance(x,list):
            for v in x: walk(v)
    walk(obj); return dict(sorted(c.items()))
def call_nodes(obj):
    result=[]
    def walk(x,path='$'):
        if isinstance(x,dict):
            if 'Call' in x and isinstance(x['Call'],dict):
                c=x['Call'].get('call',{})
                result.append({'path':path,'callee_reference':c.get('func'),
                  'argument_count':len(c.get('args',[])),'destination':c.get('dest'),
                  'has_unwind_branch':'on_unwind' in x['Call']})
            if 'Drop' in x and isinstance(x['Drop'],dict):
                result.append({'path':path,'drop_glue_reference':x['Drop'].get('fn_ptr'),
                  'has_unwind_branch':'on_unwind' in x['Drop']})
            for k,v in x.items(): walk(v,path+'/'+k)
        elif isinstance(x,list):
            for i,v in enumerate(x): walk(v,f'{path}/{i}')
    walk(obj); return result
route={
 'capture_sha256':sha(INPUT), 'has_errors':raw.get('has_errors'),
 'freeze_call':{'function_id':29,'statement_index':8,'callee_function_id':43,
                'callee_name':'core::slice::<impl>::iter','result_type':'core::slice::iter::Iter<QM31>',
                'on_unwind':'the complete statement node is preserved in r431-freeze-call-stmt-8.json'},
 'iter_wrapper':{'function_id':43,'body_form':'Structured','direct_callee_function_id':86,
                 'source_span':row(d['fun_decls'],43)['item_meta']['span']},
 'constructor':{'function_id':86,'name':'core::slice::iter::<impl>::new','body_form':'Structured',
                'source_span':row(d['fun_decls'],86)['item_meta']['span'],
                'direct_function_references':direct_ids(row(d['fun_decls'],86).get('body')),
                'operation_counts':kind_counts(row(d['fun_decls'],86).get('body'))},
 'fold_call':{'function_id':29,'statement_index':18,'callee_function_id':70,
              'callee_name':'core::slice::iter::<impl>::fold','iter_argument_local':5,
              'complete_call_node':'r431-freeze-call-stmt-18.json'},
 'fold':{'function_id':70,'body_form':'Structured','source_span':row(d['fun_decls'],70)['item_meta']['span'],
         'operation_counts':kind_counts(row(d['fun_decls'],70).get('body')),
         'direct_function_references':direct_ids(row(d['fun_decls'],70).get('body')),
         'call_nodes':call_nodes(row(d['fun_decls'],70).get('body')),
         'top_level_statement_count':len(row(d['fun_decls'],70)['body']['Structured']['body']['statements'])},
 'separate_iterator_next':{'function_id':76,'name':'core::slice::iter::<impl>::next','body_form':'Opaque',
                           'not_called_by_fold70':True},
 'properties':{'IS_ZST_global_id':31,'SIZE_global_id':32,'ZERO_global_id':14,
               'iterator_type_id':42,'element_type_id':2}
}
writej('route-operation-census.json',route)
# Capture provenance; this embeds the exact status/command records by value.
run_dir=INPUT.parent
metadata={'input_path':str(INPUT.relative_to(ROOT)),'input_sha256':sha(INPUT),
          'result_path':str((run_dir/'result.json').relative_to(ROOT)),'result_sha256':sha(run_dir/'result.json'),
          'result':read(run_dir/'result.json'),
          'command_path':str((run_dir/'extract-command.json').relative_to(ROOT)),
          'command_sha256':sha(run_dir/'extract-command.json'),
          'command':read(run_dir/'extract-command.json'),
          'launch_status_path':str((INPUT.parents[1]/'launch-status.json').relative_to(ROOT)),
          'launch_status_sha256':sha(INPUT.parents[1]/'launch-status.json')}
writej('capture-provenance.json',metadata)
# Input custody details.
writej('input-hashes.json',{
 'R431_constructor_capture':{'path':str(INPUT.relative_to(ROOT)),'sha256':sha(INPUT),'size_bytes':INPUT.stat().st_size,'has_errors':raw.get('has_errors'),'ordered_decls':len(d.get('ordered_decls',[]))},
 'R429_freeze_fold_capture':{'path':str(R429.relative_to(ROOT)),'sha256':sha(R429),'size_bytes':R429.stat().st_size,'has_errors':read(R429).get('has_errors')},
 'pinned_stdlib_inventory':{'path':str((STDLIB/'inventory.json').relative_to(ROOT)),'sha256':sha(STDLIB/'inventory.json')},
})
print('R431 indexed',len(fun_ids),'functions,',len(type_ids),'types,',len(global_ids),'globals; output',OUT)
