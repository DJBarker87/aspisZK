#!/usr/bin/env python3
"""Strict read-only projection of R431 Iter::new LLBC into an indexed command table."""
import hashlib, json
from pathlib import Path
ROOT=Path.cwd(); OUT=ROOT/'.r21-scratch/r433-actual-constructor-fragment/inventory'
INPUT=ROOT/'.r21-scratch/r431-actual-slice-construction/root-launch-a/saved-output/R431ActualSliceConstruction.llbc'
FUNCTION_ID=86; EXPECTED_STMTS=28
KNOWN_STMT_TAGS={'StorageLive','StorageDead','Assign','Switch','Return'}
KNOWN_RVALUE_TAGS={'Use','UnaryOp','RawPtr','Aggregate','BinaryOp'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
raw=read(INPUT); translated=raw['translated']; fun=translated['fun_decls'][FUNCTION_ID]
CAPTURE_RESULT=read(INPUT.parent/'result.json')
assert raw.get('has_errors') is False
assert fun['item_meta']['name'][2]['Ident'][0]=='iter'
body=fun['body']['Structured']['body']; local_rows=fun['body']['Structured']['locals']['locals']; top=body['statements']
assert len(top)==EXPECTED_STMTS, f'unexpected top-level statement count {len(top)}'
hash_defs={}; conflicts=[]
def collect(x):
    if isinstance(x,dict):
        h=x.get('HashConsedValue')
        if isinstance(h,list) and len(h)==2:
            i,v=h
            if i in hash_defs and hash_defs[i]!=v:conflicts.append(i)
            hash_defs[i]=v
        for v in x.values():collect(v)
    elif isinstance(x,list):
        for v in x:collect(v)
collect(translated)
assert not conflicts, f'conflicting hashcons definitions: {conflicts}'
def resolve_type(x,stack=()):
    if isinstance(x,dict):
        if set(x)=={'Deduplicated'}:
            i=x['Deduplicated']
            if i in stack:raise ValueError(f'cyclic dedup type reference {stack+(i,)}')
            if i not in hash_defs:raise ValueError(f'unresolved type dedup id {i}')
            return {'ResolvedDeduplicated':i,'value':resolve_type(hash_defs[i],stack+(i,))}
        if set(x)=={'HashConsedValue'}:
            i,v=x['HashConsedValue']; return {'ResolvedHashConsedValue':i,'value':resolve_type(v,stack+(i,))}
        return {k:resolve_type(v,stack) for k,v in x.items()}
    if isinstance(x,list):return [resolve_type(v,stack) for v in x]
    return x
def operand_root(place):
    current=place
    while isinstance(current,dict):
        k=current.get('kind') if 'kind' in current else current
        if not isinstance(k,dict) or len(k)!=1:return None
        tag,value=next(iter(k.items()))
        if tag in {'Local','Global'}:return {'kind':tag,'id':value if tag=='Local' else value.get('id')}
        if tag=='Projection' and isinstance(value,list) and len(value)==2:
            current=value[0];continue
        return {'kind':tag}
    return None
def operand_refs(x,path='$'):
    refs=[]
    def walk(v,p):
        if isinstance(v,dict):
            for mode in ('Copy','Move','Const'):
                if mode in v:
                    payload=v[mode]; place=payload.get('kind') if isinstance(payload,dict) else None
                    if isinstance(place,dict):
                        if 'Local' in place:refs.append({'mode':mode,'kind':'Local','index':place['Local'],'path':p+'/'+mode+'/kind','raw':place,'ty':resolve_type(payload.get('ty'))})
                        elif 'Global' in place:refs.append({'mode':mode,'kind':'Global','id':place['Global'].get('id'),'path':p+'/'+mode+'/kind','raw':place,'ty':resolve_type(payload.get('ty'))})
                        else:refs.append({'mode':mode,'kind':next(iter(place)) if place else 'unknown','root_operand':operand_root(place),'path':p+'/'+mode+'/kind','raw':place,'ty':resolve_type(payload.get('ty'))})
            for k,y in v.items():walk(y,p+'/'+k)
        elif isinstance(v,list):
            for i,y in enumerate(v):walk(y,f'{p}/{i}')
    walk(x,path);return refs
def place_desc(place):
    if not isinstance(place,dict) or 'kind' not in place:raise ValueError(f'unknown assignment destination: {place!r}')
    k=place['kind']
    if not isinstance(k,dict) or len(k)!=1:raise ValueError(f'unknown place kind: {k!r}')
    tag,val=next(iter(k.items()))
    if tag not in {'Local','Projection','Global'}:raise ValueError(f'unsupported assignment destination place {tag}')
    base=val
    if tag=='Projection':
        if not isinstance(val,list) or len(val)!=2:raise ValueError(f'unknown Projection place {val!r}')
        base=val[0]
    root_local=None
    while isinstance(base,dict) and 'kind' in base:
        bk=base['kind']
        if isinstance(bk,dict) and 'Local' in bk:root_local=bk['Local'];break
        if isinstance(bk,dict) and 'Projection' in bk and isinstance(bk['Projection'],list):base=bk['Projection'][0];continue
        break
    return {'place_kind':tag,'local_alias':val if tag=='Local' else root_local,
            'raw_place':place,'raw_place_type':place.get('ty'),'resolved_place_type':resolve_type(place.get('ty'))}
def nested_ops(x):
    tags=[]
    def walk(v):
        if isinstance(v,dict):
            for k,y in v.items():
                if k in {'Transmute','Cast','RawPtr','BinaryOp','UnaryOp','Aggregate','Ref','PtrMetadata','Deref','Projection','Field','Global','Local','Copy','Move','Const'}:tags.append(k)
                walk(y)
        elif isinstance(v,list):
            for y in v:walk(y)
    walk(x);return tags
def resolved_type_fields(x):
    out=[]
    def walk(v,path='$'):
        if isinstance(v,dict):
            for k,y in v.items():
                if k=='ty':out.append({'path':path+'/ty','raw_type':y,'resolved_type':resolve_type(y)})
                walk(y,path+'/'+k)
        elif isinstance(v,list):
            for i,y in enumerate(v):walk(y,f'{path}/{i}')
    walk(x);return out
def count_stmt_tree(items):
    total=0
    for item in items:
        total+=1
        if item['opcode']=='Switch':
            total+=count_stmt_tree(item['then_arm']['statements'])
            total+=count_stmt_tree(item['else_arm']['statements'])
    return total
def rvalue_desc(x):
    if not isinstance(x,dict) or len(x)!=1:raise ValueError(f'unknown rvalue shape: {x!r}')
    opcode=next(iter(x))
    if opcode not in KNOWN_RVALUE_TAGS:raise ValueError(f'unknown rvalue opcode {opcode}')
    return {'opcode':opcode,'raw_rvalue':x,'operand_references':operand_refs(x),'resolved_type_fields':resolved_type_fields(x),'nested_operation_tags':nested_ops(x)}
def block_desc(block,path):
    if not isinstance(block,dict) or not isinstance(block.get('statements'),list):raise ValueError(f'unknown branch block at {path}')
    return {'span':block.get('span'),'statements':[stmt_desc(s,f'{path}/statements/{i}') for i,s in enumerate(block['statements'])]}
def stmt_desc(s,path):
    if not isinstance(s,dict):raise ValueError(f'unknown statement shape at {path}')
    k=s.get('kind')
    if isinstance(k,str):tag,payload=k,None
    elif isinstance(k,dict) and len(k)==1:tag,payload=next(iter(k.items()))
    else:raise ValueError(f'unknown statement shape at {path}')
    if tag not in KNOWN_STMT_TAGS:raise ValueError(f'unknown statement tag {tag} at {path}')
    d={'path':path,'statement_id':s.get('id'),'span':s.get('span'),'comments_before':s.get('comments_before',[]),'opcode':tag}
    if tag in {'StorageLive','StorageDead'}:
        d.update({'local':payload,'local_type':resolve_type(local_rows[payload]['ty'])})
    elif tag=='Assign':
        if not isinstance(payload,list) or len(payload)!=2:raise ValueError(f'unknown Assign form at {path}')
        d.update({'destination':place_desc(payload[0]),'rvalue':rvalue_desc(payload[1])})
    elif tag=='Switch':
        if not isinstance(payload,dict) or len(payload)!=1 or 'If' not in payload:raise ValueError(f'unknown Switch form at {path}')
        a=payload['If']
        if not isinstance(a,list) or len(a)!=3:raise ValueError(f'unknown If arm structure at {path}')
        cond,yes,no=a
        d.update({'condition':cond,'condition_operand_references':operand_refs(cond),'then_arm':block_desc(yes,path+'/then'),'else_arm':block_desc(no,path+'/else')})
    elif tag=='Return' and payload is not None:raise ValueError(f'unknown Return payload at {path}: {payload!r}')
    return d
table=[stmt_desc(s,f'fun{FUNCTION_ID}/statements/{i}') for i,s in enumerate(top)]
assert sum(1 for x in table if x['opcode']=='Switch')==1
assert table[18]['opcode']=='Switch' and table[18]['condition_operand_references'][0]['kind']=='Global'
(OUT/'constructor86-raw-function-row.json').write_text(json.dumps(fun,indent=2,sort_keys=True)+'\n')
(OUT/'constructor86-raw-top-level-statements.json').write_text(json.dumps(top,indent=2,sort_keys=True)+'\n')
dump(OUT/'constructor86-command-table.json',{
 'input_path':str(INPUT.relative_to(ROOT)),'input_sha256':sha(INPUT),'has_errors':raw['has_errors'],
 'function_id':FUNCTION_ID,'qualified_name':'core::slice::iter::<impl>::new','source_span':fun['item_meta']['span'],
 'source_file_record':translated['files'][fun['item_meta']['span']['data']['file_id']],
 'capture_source_revision':CAPTURE_RESULT.get('capture_revision'),'capture_exit':CAPTURE_RESULT.get('charon_exit_status'),
 'capture_wall_time':CAPTURE_RESULT.get('wall_time'),'capture_peak_rss_kib':CAPTURE_RESULT.get('peak_rss_kib'),'capture_swap_count':CAPTURE_RESULT.get('swap_count'),
 'signature':fun['signature'],'resolved_signature':resolve_type(fun['signature']),
 'top_level_statement_count':len(top),'statement_count_including_switch_arms':count_stmt_tree(table),
 'hashcons_definition_count':len(hash_defs),'statement_commands':table,
 'policy':'No operation is lowered or erased. Raw nodes remain authoritative alongside descriptors.'})
print('table generated',len(table),'top-level statements; branch arms included')
