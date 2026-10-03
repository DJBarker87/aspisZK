#!/usr/bin/env python3
"""Expand and inventory only frozen R437 Fun70/Fun112 borrow/callback rows."""
import collections, hashlib, json
from pathlib import Path

ROOT=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
O=Path(__file__).resolve().parent
LLBC=O/'input/R437PointerWrapperLayout.llbc'
T=json.loads(LLBC.read_text())
translated=T['translated']
R437I=json.loads((ROOT/'.r21-scratch/r437-pointer-source-boundary/inventory/inventory.json').read_text())

# Build and validate the serialized hash-cons table.
hc={}
def walk(v,path=()):
    if isinstance(v,dict):
        if set(v)=={'HashConsedValue'}:
            pair=v['HashConsedValue']
            if not isinstance(pair,list) or len(pair)!=2 or not isinstance(pair[0],int):
                raise ValueError(f'malformed HashConsedValue at {path}')
            i,x=pair
            if i in hc and hc[i]!=x: raise ValueError(f'conflicting hashcons id {i}')
            hc[i]=x
        for k,x in v.items(): yield path+(k,),x; yield from walk(x,path+(k,))
    elif isinstance(v,list):
        for i,x in enumerate(v): yield path+(i,),x; yield from walk(x,path+(i,))
for p,n in walk(translated): pass

def decode(v,active=()):
    if isinstance(v,dict):
        if set(v)=={'HashConsedValue'}:
            pair=v['HashConsedValue']
            if not isinstance(pair,list) or len(pair)!=2: raise ValueError('malformed HashConsedValue')
            return decode(pair[1],active)
        if set(v)=={'Deduplicated'}:
            i=v['Deduplicated']
            if not isinstance(i,int) or i not in hc: raise ValueError(f'unresolved Deduplicated {i!r}')
            if i in active: raise ValueError(f'cyclic hashcons expansion {active+(i,)}')
            return decode(hc[i],active+(i,))
        return {k:decode(x,active) for k,x in v.items()}
    if isinstance(v,list): return [decode(x,active) for x in v]
    return v

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def jsonwrite(name,obj): (O/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def fmtpath(path):
    s=''
    for x in path:
        if isinstance(x,int): s+=f'[{x}]'
        elif s: s+='.'+str(x)
        else: s=str(x)
    return s

def statement_nodes(root,path=()):
    """Yield all structured statement records, including nested cleanup lists."""
    if isinstance(root,dict):
        if all(k in root for k in ('span','kind','comments_before')) and isinstance(root.get('kind'),(dict,str)):
            yield path,root
        for k,v in root.items(): yield from statement_nodes(v,path+(k,))
    elif isinstance(root,list):
        for i,v in enumerate(root): yield from statement_nodes(v,path+(i,))

EVENT_TAGS={
 'Assign','Call','Switch','Loop','Drop','StorageLive','StorageDead','Assert','Break','Continue','Return',
 'Copy','Move','Ref','Borrow','Deref','Field','Index','Projection','RawPtr','Aggregate','UnaryOp','BinaryOp',
 'Global','SetDiscriminant','EndBorrow','Panic','Abort','UnwindResume','Constant','Use','PtrMetadata'
}
def events(root,path=()):
    if isinstance(root,dict):
        if len(root)==1:
            k=next(iter(root))
            if k in EVENT_TAGS:
                yield path,k,root[k]
        for k,v in root.items(): yield from events(v,path+(k,))
    elif isinstance(root,list):
        for i,v in enumerate(root): yield from events(v,path+(i,))

def loc_summary(payload):
    if isinstance(payload,dict) and 'kind' in payload:
        return {'place_kind':payload.get('kind'),'place_type':payload.get('ty')}
    if isinstance(payload,list): return {'arity':len(payload),'value':payload}
    return payload

rows={}
for fid in (70,112):
    row=translated['fun_decls'][fid]
    if row is None or row.get('def_id')!=fid: raise ValueError(f'Fun{fid} missing/mismatched')
    rows[fid]=decode(row)

# Keep exact selected declaration records and related type/trait rows from the input.
type_ids=(50,)
trait_ids=(3,)
impl_ids=(35,)
selected={
 'input_llbc':{'path':str(LLBC.relative_to(ROOT)),'sha256':sha(LLBC),'has_errors':T.get('has_errors'),'charon_version':T.get('charon_version')},
 'source_file_0':{'name':translated['files'][0]['name'],'crate_name':translated['files'][0]['crate_name'],'source_sha256':hashlib.sha256(translated['files'][0]['contents'].encode()).hexdigest(),'body_excerpt':'lines 126-139 in frozen relation_callback.rs'},
 'source_file_40':{'name':translated['files'][40]['name'],'crate_name':translated['files'][40]['crate_name'],'contents_present':translated['files'][40]['contents'] is not None,'note':'rustc core source file was not embedded in this LLBC input'},
 'functions':{str(k):v for k,v in rows.items()},
 'types':{str(i):decode(translated['type_decls'][i]) for i in type_ids},
 'trait_declarations':{str(i):decode(translated['trait_decls'][i]) for i in trait_ids},
 'trait_implementations':{str(i):decode(translated['trait_impls'][i]) for i in impl_ids},
 'scope_note':'Original LLBC rows are preserved by input file; this file resolves hash-cons indirections only. No operation or source semantics are inferred.'
}
jsonwrite('selected-functions-expanded.json',selected)

all_rows=[]; event_rows=[]
for fid,row in rows.items():
 body=row['body']
 if not isinstance(body,dict) or 'Structured' not in body: raise ValueError(f'Fun{fid} not structured')
 b=body['Structured']
 for path,st in statement_nodes(b['body']['statements'],('body','Structured','body','statements')):
  kind=st['kind']
  if isinstance(kind,dict) and len(kind)==1: tag,payload=next(iter(kind.items()))
  elif isinstance(kind,str): tag,payload=kind,None
  else: raise ValueError(f'unknown statement kind shape Fun{fid} {path}: {kind!r}')
  all_rows.append({'row':len(all_rows),'fun_id':fid,'statement_path':fmtpath(path),'statement_id':st.get('id'),'span':st.get('span'),'statement_kind':tag,'payload':payload,'comments_before':st.get('comments_before',[])})
  for ep,etag,payload2 in events(kind,()):
   event_rows.append({'event':len(event_rows),'fun_id':fid,'statement_path':fmtpath(path),'statement_id':st.get('id'),'statement_kind':tag,'event_path':fmtpath(path+('kind',)+ep),'tag':etag,'payload':payload2})
jsonwrite('statement-operation-table.json',all_rows)
jsonwrite('nested-operation-event-table.json',event_rows)

# Human-readable exhaustive index: every statement and nested cleanup statement,
# then every recognized operation/projection event with the complete JSON payload
# available in the machine table.
md=['# R438 Fun70/Fun112 borrow and callback operation inventory','',
 f'Input LLBC SHA-256: `{sha(LLBC)}`; Charon version `{T.get("charon_version")}`; has_errors `{T.get("has_errors")}`.',
 f'Expanded statement rows: {len(all_rows)}. Nested operation/projection events: {len(event_rows)}.',
 'Each row in the JSON tables carries its complete decoded payload. Statement paths include control-flow and nested `on_unwind` statement lists. The event table is intentionally tag-oriented: `Ref` may denote a type constructor if its event path is under a type field; inspect the complete path and payload rather than treating all such tags as runtime reference operations.', '',
 '## Statement table', '', '|#|Fun|statement id|span|kind|path|', '|---:|---:|---:|---|---|---|']
for x in all_rows:
 sp=x['span'] or {}; d=sp.get('data',{}); beg=d.get('beg',{})
 loc=f"file{d.get('file_id')}:{beg.get('line')}:{beg.get('col')}" if d else ''
 md.append(f"|{x['row']}|{x['fun_id']}|{x['statement_id']}|{loc}|{x['statement_kind']}|`{x['statement_path']}`|")
md+=['','## Operation/projection event table','','|#|Fun|statement id|statement kind|event tag|event path|','|---:|---:|---:|---|---|---|']
for x in event_rows:
 md.append(f"|{x['event']}|{x['fun_id']}|{x['statement_id']}|{x['statement_kind']}|{x['tag']}|`{x['event_path']}`|")
(O/'operation-tables.md').write_text('\n'.join(md)+'\n')

# Exact implementation excerpts from the saved pinned Aeneas candidate sources.
source_ranges={
 'InterpExpressions.ml':[(176,248,'copy_value borrow/loan handling'),(379,424,'operand reorganization and evaluation entry point'),(580,613,'Copy/Move operand evaluation and place update'),(614,645,'operand evaluation entry points'),(1222,1303,'shared and mutable reference creation'),(1489,1515,'rvalue dispatch')],
 'InterpPaths.ml':[(100,210,'place projection and Ref/Deref access'),(265,305,'place access recursion and backward update'),(307,378,'Read/Write/Move access policy and read/write place')],
 'InterpStatements.ml':[(420,475,'call argument evaluation, frame setup, dispatch, frame return'),(908,990,'assignment, place write, Drop, StorageDead')],
}
ex=[]
for name,ranges in source_ranges.items():
 p=O/'pinned-aeneas'/name; lines=p.read_text().splitlines()
 ex.append(f'\n## {name} — SHA256 {sha(p)}\n')
 for lo,hi,label in ranges:
  ex.append(f'\n### Lines {lo}-{hi}: {label}\n')
  ex.extend(f'{i:5d} {lines[i-1]}\n' for i in range(lo,min(hi,len(lines))+1))
 (O/'aeneas-reference-excerpts.txt').write_text(''.join(ex))

# Extract complete place chains from each immediate statement body. Nested
# statements are independently indexed, so remove their containers while
# scanning a parent statement to avoid double-counting child operations.
def strip_child_statements(v):
    if isinstance(v,dict):
        return {k:strip_child_statements(x) for k,x in v.items() if k!='statements'}
    if isinstance(v,list): return [strip_child_statements(x) for x in v]
    return v
def place_shape(p):
    k=p.get('kind') if isinstance(p,dict) else None
    projections=[]
    while isinstance(k,dict) and set(k)=={'Projection'}:
        pair=k['Projection']
        if not isinstance(pair,list) or len(pair)!=2: raise ValueError('malformed place Projection')
        base,elem=pair
        projections.append(elem)
        k=base.get('kind') if isinstance(base,dict) else None
        p=base
    projections.reverse()
    if isinstance(k,dict) and len(k)==1: base_tag,base_payload=next(iter(k.items()))
    else: base_tag,base_payload='unknown',k
    return {'base_kind':base_tag,'base_payload':base_payload,'projections':projections,'final_type':p.get('ty') if isinstance(p,dict) else None}
def place_roots(v,path=()):
    if isinstance(v,dict):
        k=v.get('kind')
        if isinstance(k,dict) and len(k)==1 and next(iter(k)) in ('Local','Projection','Global') and 'ty' in v:
            # A nested Projection's base is itself place-shaped; emit only the
            # outermost complete place root, identified by its parent key.
            yield path,v
            return
        for key,x in v.items(): yield from place_roots(x,path+(key,))
    elif isinstance(v,list):
        for i,x in enumerate(v): yield from place_roots(x,path+(i,))

place_rows=[]; assign_rows=[]; call_rows=[]; ref_rvalue_rows=[]; drop_rows=[]
for fid,row in rows.items():
    body=row['body']['Structured']['body']['statements']
    b=rows[fid]['body']['Structured']
    for path,st in statement_nodes(body,('body','Structured','body','statements')):
        kind=st['kind']; kind_tag=next(iter(kind)) if isinstance(kind,dict) and len(kind)==1 else kind
        own=strip_child_statements(kind)
        for relpath,p in place_roots(own):
            place_rows.append({'fun_id':fid,'statement_id':st.get('id'),'statement_path':fmtpath(path),'place_path':fmtpath(('kind',)+relpath),'place':place_shape(p),'raw_place':p})
        if kind_tag=='Assign':
            lhs,rhs=kind['Assign']
            rhs_tag=next(iter(rhs)) if isinstance(rhs,dict) and len(rhs)==1 else None
            rec={'fun_id':fid,'statement_id':st.get('id'),'statement_path':fmtpath(path),'lhs':place_shape(lhs),'rhs_tag':rhs_tag,'rhs':rhs}
            assign_rows.append(rec)
            if rhs_tag=='Ref': ref_rvalue_rows.append(rec)
        if kind_tag=='Call':
            call=kind['Call']['call']
            rec={'fun_id':fid,'statement_id':st.get('id'),'statement_path':fmtpath(path),'func':call.get('func'),'args':call.get('args'),'dest':call.get('dest'),'has_unwind':bool(kind['Call'].get('on_unwind')),'call':call,'on_unwind':kind['Call'].get('on_unwind')}
            call_rows.append(rec)
        if kind_tag=='Drop': drop_rows.append({'fun_id':fid,'statement_id':st.get('id'),'statement_path':fmtpath(path),'drop':kind['Drop']})
jsonwrite('place-projection-table.json',place_rows)
jsonwrite('assignment-call-drop-table.json',{'assignments':assign_rows,'rvalue_refs':ref_rvalue_rows,'calls':call_rows,'drops':drop_rows})

# Focused facts are literal serialized AST selections, accompanied by the full
# decoded bodies and tables above. No typing or execution relationship inferred.
def find_fun35_call():
    matches=[]
    for x in call_rows:
        if x['fun_id']!=70: continue
        # In this schema a trait function stores [trait_ref, method_id].
        reg=x['func'].get('Regular',{}) if isinstance(x['func'],dict) else {}
        trait=reg.get('kind',{}).get('Trait')
        if isinstance(trait,list) and len(trait)==2:
            ref=trait[0]
            impl=ref.get('kind',{}).get('TraitImpl',{}) if isinstance(ref,dict) else {}
            if impl.get('id')==35 and trait[1]==0: matches.append(x)
    return matches
fnmut_dispatch=find_fun35_call()
if len(fnmut_dispatch)!=1: raise ValueError(f'expected one FnMut impl35 method0 call, found {len(fnmut_dispatch)}')
args=fnmut_dispatch[0]['args']
if fnmut_dispatch[0]['statement_id']!=10502 or len(args)!=2 or any(
 not isinstance(a,dict) or set(a)!={'Move'} or a['Move'].get('kind')!={'Local':i}
 for a,i in zip(args,(17,18))
): raise ValueError('Fun70 FnMut dispatch statement/operand shape changed')
for fid,expected in {112:{11907,11909,11915,11923,11928,11930,11936,11939,11941}}.items():
 present={x['statement_id'] for x in all_rows if x['fun_id']==fid}
 if not expected <= present: raise ValueError(f'Fun{fid} expected callback statement ids absent: {expected-present}')
facts={
 'source_and_llbc':selected['input_llbc'],
 'frozen_relation_callback_sha256':selected['source_file_0']['source_sha256'],
'functions':{str(i):{'name':rows[i]['item_meta']['name'],'span':rows[i]['item_meta']['span'],'source':rows[i].get('src'),'body_kind':list(rows[i]['body'].keys()),'local_count':len(rows[i]['body']['Structured']['locals']['locals'])} for i in (70,112)},
 'fnmut_dispatch_in_fold':fnmut_dispatch[0],
 'fun112_structural_facts':{
   'capture_power_read_statement_ids':[11907,11928],
   'capture_gamma_read_statement_id':11930,
   'mul_call_statement_ids':[11915,11936],
   'accumulate_call_statement_id':11923,
   'captured_power_write_statement_id':11939,
   'return_copy_statement_id':11941,
   'complete_unwind_and_drop_paths':'See statement-operation-table.json and assignment-call-drop-table.json; every nested statement in the selected body is enumerated.'
 },
 'counts':{'all_statement_records':len(all_rows),'operation_projection_events':len(event_rows),'place_roots':len(place_rows),'assignments':len(assign_rows),'rvalue_ref_assignments':len(ref_rvalue_rows),'calls':len(call_rows),'drops':len(drop_rows)},
 'boundary':'Exact decoded LLBC AST/path inventory only; no aliasing, lifetime, dispatch semantics, correctness, or source-to-model correspondence conclusion.'
}
jsonwrite('focused-facts.json',facts)

# Cross-check source file 0 is the frozen R434 source and capture locations.
source_text=translated['files'][0]['contents']
if hashlib.sha256(source_text.encode()).hexdigest()!='4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f':
 raise ValueError('embedded source file 0 differs from pinned relation_callback receipt')
report={
 'input_llbc':selected['input_llbc'],
 'function_ids':[70,112],
 'source_file_0':selected['source_file_0'],
 'source_file_40':selected['source_file_40'],
 'declaration_rows':{'type_ids':list(type_ids),'trait_decl_ids':list(trait_ids),'trait_impl_ids':list(impl_ids)},
 'pinned_aeneas':{'root':R437I['pinned_roots']['aeneas_candidate'],'source_files':{n:{'path':R437I['source_files']['aeneas/'+n]['pinned_source_path'],'sha256':sha(O/'pinned-aeneas'/n)} for n in source_ranges}},
 'counts':{'statement_records_including_nested_cleanup':len(all_rows),'operation_and_projection_events':len(event_rows),'fun70_statement_records':sum(x['fun_id']==70 for x in all_rows),'fun112_statement_records':sum(x['fun_id']==112 for x in all_rows)},
 'aeneas_sources':{n:{'path':str((O/'pinned-aeneas'/n).relative_to(ROOT)),'sha256':sha(O/'pinned-aeneas'/n)} for n in source_ranges},
 'facts_boundary':'Serialized LLBC rows and pinned interpreter source branches only. No assumptions about borrow identity, aliasing, lifetime, callback equivalence, or Rust-to-LLBC correspondence.'
}
outputs={n:{'sha256':sha(O/n),'size_bytes':(O/n).stat().st_size} for n in ['selected-functions-expanded.json','statement-operation-table.json','nested-operation-event-table.json','operation-tables.md','place-projection-table.json','assignment-call-drop-table.json','aeneas-reference-excerpts.txt','focused-facts.json']}
report['outputs']=outputs
jsonwrite('borrow-inventory.json',report)

readme='''# R438 selected Fun70/Fun112 borrow and callback inventory

This is a read-only inventory of the exact R437 LLBC input selected by the R438 FnMut source-selection task. Input SHA-256, source rows, function identities, and generated artifact hashes are in `borrow-inventory.json`. The frozen source `relation_callback.rs` and full LLBC are copied under `input/`; the exact Fun70 and Fun112 records are preserved in `selected-functions-expanded.json` after resolving only serialized hash-cons indirections. The original LLBC remains byte-for-byte in `input/R437PointerWrapperLayout.llbc`.

`statement-operation-table.json` enumerates every structured statement in Fun70 and Fun112, including nested branch/loop statements and unwind cleanup lists. `nested-operation-event-table.json` records all recognized operation/projection tags with exact paths and payloads. Because tag names such as `Ref` may also occur in type nodes, the path is part of each fact. `place-projection-table.json` lists complete place roots and every projection in order; `assignment-call-drop-table.json` retains complete assignment, call, and drop payloads (including unwind trees).

The selected fold callback is one trait call in Fun70: it references trait impl 35 / method 0 and passes `Move(Local17), Move(Local18)` to destination Local16. Fun112 is the corresponding captured closure `call_mut` body. Its serialized places read captured Type50 field 0 through a mutable-reference field and read field 1 through a shared-reference field; statement 11939 writes the moved result through the field-0 dereference. Calls at 11915, 11923, and 11936 preserve their complete unwind lists. These statements identify AST structure only.

`aeneas-reference-excerpts.txt` gives exact line excerpts from the pinned Aeneas candidate's operand copy/move evaluator, reference creation, projection/dereference and backward-update logic, and call/frame/assignment/drop handling. Source hashes are printed with each excerpt and indexed in `borrow-inventory.json`. For example, Aeneas `copy_value` handles shared borrows by making a fresh shared-borrow id and explicitly errors on a mutable-borrow copy; `eval_rvalue_ref` has separate shared and mutable creation branches; and `InterpPaths` maps Read/Write/Move to different loan/borrow traversal permissions. These are interpreter-source facts, not a derived correspondence theorem.

The Fun70 span points into `/rustc/library/core/src/slice/iter/macros.rs`, whose source text is not embedded in this LLBC. No Rust source operation is reconstructed from the span. This inventory makes no alias, lifetime, frame, callback, pointer, source-semantics, or security conclusion.
'''
(O/'README.md').write_text(readme)
# The manifest covers every regular file in this inventory directory except
# itself, including the fully preserved raw input and Aeneas source excerpts.
import subprocess
subprocess.run("find . -type f ! -path './SHA256SUMS' -print0 | sort -z | xargs -0 shasum -a 256 > SHA256SUMS",shell=True,cwd=O,check=True)
print(json.dumps({'statement_records':len(all_rows),'event_records':len(event_rows),'place_roots':len(place_rows),'assignments':len(assign_rows),'calls':len(call_rows),'drops':len(drop_rows),'outputs':outputs},indent=2))
