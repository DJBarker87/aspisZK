#!/usr/bin/env python3
"""Lossless selected-row snapshot and mechanical inventory; no normalization."""
from pathlib import Path
import json,hashlib,collections
HERE=Path(__file__).parent
src=HERE.parent/'saved-output'/'R428SliceNextSource.llbc'
data=json.loads(src.read_text())
t=data['translated']
# Exact path selector: source module and final `next` item, not a table index alone.
def name_text(name):
    out=[]
    for e in name or []:
        if 'Ident' in e: out.append(e['Ident'][0])
        elif 'Impl' in e: out.append('impl')
        elif 'Instantiated' in e: out.append('instantiated')
    return '::'.join(out)
rows=[]
for i,f in enumerate(t['fun_decls']):
    if f is None: continue
    raw_name=f.get('item_meta',{}).get('name') or []
    ids=[e['Ident'][0] for e in raw_name if 'Ident' in e]
    nm=name_text(raw_name)
    if ids[:3]==['core','slice','iter'] and ids[-1:] == ['next']:
        rows.append((i,f,nm))
if not rows: raise SystemExit('no selected concrete SliceIter::next row')
# Keep all matching declarations byte-structurally as decoded by JSON.
selected=[]
for i,f,nm in rows:
    body=f['body'].get('Structured') if isinstance(f.get('body'),dict) else None
    kind_counts=collections.Counter(); rvalue_counts=collections.Counter(); calls=[]; global_refs=[]; const_nodes=[]
    def walk(x,path=''):
        if isinstance(x,dict):
            kv=x.get('kind')
            if isinstance(kv,dict):
                for k,v in kv.items(): kind_counts[k]+=1
                if 'Assign' in kv and isinstance(kv['Assign'],list) and len(kv['Assign'])>1:
                    rv=kv['Assign'][1]
                    if isinstance(rv,dict): rvalue_counts.update(rv.keys())
            if 'Call' in x and isinstance(x['Call'],dict): calls.append({'path':path,'call':x['Call']})
            if 'Global' in x and isinstance(x['Global'],dict): global_refs.append({'path':path,'global_ref':x['Global']})
            if 'Const' in x and isinstance(x['Const'],dict): const_nodes.append({'path':path,'const':x['Const']})
            for k,v in x.items(): walk(v,path+'/'+k)
        elif isinstance(x,list):
            for j,v in enumerate(x): walk(v,path+f'/{j}')
    if body: walk(body)
    # Resolve exact directly referenced declaration metadata, keeping ids.
    resolved_calls=[]
    for rec in calls:
        call=rec['call']['call']
        fn=call['func']['Regular']
        fk=fn['kind']
        if 'Fun' in fk:
            ref=fk['Fun'].get('Regular')
            decl=t['fun_decls'][ref] if isinstance(ref,int) and ref<len(t['fun_decls']) else None
            resolved_calls.append({**rec,'function_id':ref,'function_name':name_text(decl.get('item_meta',{}).get('name')) if decl else None,'body_tag':next(iter(decl['body'])) if decl and isinstance(decl.get('body'),dict) else decl.get('body') if decl else None,'opacity':decl.get('item_meta',{}).get('opacity') if decl else None})
    resolved_globals=[]
    for rec in global_refs:
        gid=rec['global_ref'].get('id'); decl=t['global_decls'][gid] if isinstance(gid,int) and gid<len(t['global_decls']) else None
        resolved_globals.append({**rec,'global_id':gid,'global_name':name_text(decl.get('item_meta',{}).get('name')) if decl else None,'global_kind':decl.get('global_kind') if decl else None,'body_tag':next(iter(decl['value']['kind'])) if decl and isinstance(decl.get('value'),dict) and isinstance(decl['value'].get('kind'),dict) else None,'opacity':decl.get('item_meta',{}).get('opacity') if decl else None})
    selected.append({'id':i,'qualified_name':'core::slice::iter::{impl-trait#5}::next (instantiated)' if i==10 else nm,'source':f.get('src'),'source_span':f.get('item_meta',{}).get('span'),'is_local':f.get('item_meta',{}).get('is_local'),'opacity':f.get('item_meta',{}).get('opacity'),'body_kind':next(iter(f['body'])) if isinstance(f.get('body'),dict) else f.get('body'),'generics':f.get('generics'),'signature':f.get('signature'),'body_span':body.get('span') if body else None,'local_count':len(body.get('locals',{}).get('locals',[])) if body else None,'top_level_statement_count':len(body.get('body',{}).get('statements',[])) if body else None,'body_kind_tag_counts':dict(kind_counts),'assignment_rvalue_tag_counts':dict(rvalue_counts),'direct_function_calls':resolved_calls,'global_references':resolved_globals,'literal_const_occurrence_count':len(const_nodes),'complete_decoded_declaration':f})
# Exact dependencies inspected from the body/global, plus B and Iter/Option type instances for transparent identity.
dep_ids={'functions':sorted({c['function_id'] for x in selected for c in x['direct_function_calls'] if x['direct_function_calls']}),'globals':sorted({g['global_id'] for x in selected for g in x['global_references'] if x['global_references']})}
func_deps={i:t['fun_decls'][i] for i in dep_ids['functions']}
global_deps={i:t['global_decls'][i] for i in dep_ids['globals']}
types={i:t['type_decls'][i] for i in [0,6,9,12,13] if i<len(t['type_decls']) and t['type_decls'][i] is not None}
# IS_ZST's initializer may call an opaque function; preserve the declaration, and inventory that reference exactly.
for gid,g in global_deps.items():
    if 'IS_ZST' in name_text(g['item_meta']['name']):
        val=g.get('value',{}).get('kind',{})
        if 'Call' in val:
            ref=val['Call'][0].get('kind',{}).get('Fun',{}).get('Regular')
            if isinstance(ref,int): func_deps[ref]=t['fun_decls'][ref]
wanted_hc={465,787,924,925}
hashcons={}
def scan_hc(x):
    if isinstance(x,dict):
        h=x.get('HashConsedValue')
        if isinstance(h,list) and len(h)==2 and h[0] in wanted_hc: hashcons[h[0]]=h[1]
        for v in x.values(): scan_hc(v)
    elif isinstance(x,list):
        for v in x: scan_hc(v)
scan_hc(data)
out={'input':{'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'charon_version':data.get('charon_version'),'capture_source_commit':json.loads((HERE.parent/'saved-output'/'result.json').read_text()).get('source_commit')},'source_files':{i:t['files'][i] for i in [23,31,32]},'hashcons_values':hashcons,'match_rule':'qualified module path core::slice::iter and final ident next; exact declaration rows preserved, no normalization','matching_next_declarations':selected,'resolved_direct_dependencies':{'functions':func_deps,'globals':global_deps,'type_declarations':types},'notes':{'zst_global_is_literal':False,'zst_global_status':'NamedConst with Foreign opacity and value Call(Regular Fun 43); inspect its saved function row for body status','declaration_body_status_only':'records Charon output; no claim of Rust correctness'}}
(HERE/'inventory.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','input_sha256':out['input']['sha256'],'matching_next_rows':[{'id':x['id'],'name':x['qualified_name'],'body_kind':x['body_kind'],'opacity':x['opacity'],'source':x['source_span'],'direct_calls':x['direct_function_calls'],'global_refs':x['global_references']} for x in selected],'body_kind_tag_counts':selected[0]['body_kind_tag_counts']},indent=2))
