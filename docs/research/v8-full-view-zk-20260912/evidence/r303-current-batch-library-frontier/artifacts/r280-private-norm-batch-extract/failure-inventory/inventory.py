#!/usr/bin/env python3
"""Read-only inventory of the saved R280 Charon Zip trait-clause error."""
import hashlib,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parent
LLBC=ROOT/'R280PrivateNormBatch.llbc'
LOG=ROOT/'extract.log'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
doc=json.loads(LLBC.read_text()); t=doc['translated']
assert doc['has_errors'] is True
COL={'Type':'type_decls','Fun':'fun_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}
rows={(k,r['def_id']):r for k,key in COL.items() for r in t.get(key,[]) if isinstance(r,dict) and isinstance(r.get('def_id'),int)}
# Resolve hash-consed values once so paths and references are traversed by meaning.
table={}
def index(x):
    if isinstance(x,dict):
        if set(x)=={'HashConsedValue'} and isinstance(x['HashConsedValue'],list):
            i,v=x['HashConsedValue']; table[i]=v
        for v in x.values(): index(v)
    elif isinstance(x,list):
        for v in x:index(v)
index(doc)
def expand(x,stack=()):
    if isinstance(x,dict):
        if set(x)=={'HashConsedValue'}:
            i,v=x['HashConsedValue']; assert i not in stack
            return expand(v,stack+(i,))
        if set(x)=={'Deduplicated'}:
            i=x['Deduplicated']; assert i in table and i not in stack
            return expand(table[i],stack+(i,))
        return {k:expand(v,stack) for k,v in x.items()}
    if isinstance(x,list): return [expand(v,stack) for v in x]
    return x
# Item labels/source file table are only used to render IDs and spans.
labels={}
for e in t.get('item_names',[]):
    key=e.get('key',{})
    if len(key)==1:
        kind,ident=next(iter(key.items()))
        parts=[]
        for p in e.get('value',[]):
            if isinstance(p,dict) and 'Ident' in p: parts.append(p['Ident'][0])
            elif isinstance(p,dict) and 'Impl' in p: parts.append(str(p['Impl']))
        labels[(kind,ident)]='::'.join(parts)
files={f.get('id'):f.get('name') for f in t.get('files',[]) if isinstance(f,dict) and isinstance(f.get('id'),int)}

def span(kind,i):
    meta=rows[(kind,i)].get('item_meta',{})
    raw=meta.get('span',{}).get('data',{})
    return {'file_id':raw.get('file_id'),'file':files.get(raw.get('file_id')),'beg':raw.get('beg'),'end':raw.get('end')}

def name(kind,i): return labels.get((kind,i),f'{kind}{i}')
def suppressed(row):
    src=expand(row.get('src'))
    if not isinstance(src,dict):return None
    if 'TraitImpl' in src:
        i=src['TraitImpl'].get('impl_ref',{}).get('id'); return ('TraitImpl',i) if isinstance(i,int) else None
    if 'TraitDecl' in src:
        i=src['TraitDecl'].get('trait_ref',{}).get('id'); return ('TraitDecl',i) if isinstance(i,int) else None
    return None

def payload(node):
    k,i=node; r=expand(rows[node])
    if k=='Fun':
        fs={q:r[q] for q in ('generics','signature','body')}
        src=r.get('src')
        if isinstance(src,dict) and 'TraitDecl' in src:
            ti=src['TraitDecl'].get('trait_ref',{}).get('id')
            if isinstance(ti,int): fs['_explicit_trait_source_edge']={'trait_decl_ref':{'skip_binder':{'id':ti}}}
        return fs
    if k=='TraitDecl':
        fs={q:r[q] for q in ('generics','implied_clauses','types','vtable')}
        for j,c in enumerate(r.get('consts',[])):
            fs[f'const{j}.ty']=c['ty']
            if c.get('default') is not None:
                fs[f'const{j}.default.generics']=c['default'].get('generics',{})
                fs[f'_node_const_default_{j}']={'Global':c['default']['id']}
        for j,m in enumerate(r.get('methods',[])):
            if m is None:continue
            fs[f'method{j}.params']=m['params']; fs[f'method{j}.signature']=m['skip_binder']['signature']
            if m['skip_binder'].get('default') is not None:
                fs[f'method{j}.default.generics']=m['skip_binder']['default'].get('generics',{})
                fs[f'_node_method_default_{j}']={'Fun':{'Regular':m['skip_binder']['default']['id']}}
        return fs
    return {q:v for q,v in r.items() if q not in ('def_id','item_meta','src','is_global_initializer')}

def graph_from(root):
    edges={}; reach_only={}; active=[]; visited=set(); cycles=[]; missing=[]; unknown=[]
    def record(owner,target,path,reach=False):
        if target not in rows:
            missing.append({'owner':list(owner),'path':path,'target':list(target)}); return
        (reach_only if reach else edges).setdefault(owner,set()).add(target)
    def walk(x,owner,path,suppress,reach=False):
        if isinstance(x,list):
            for j,v in enumerate(x):walk(v,owner,f'{path}[{j}]',suppress,reach)
            return
        if not isinstance(x,dict):return
        if 'Adt' in x:
            v=x['Adt']
            if isinstance(v,int):record(owner,('Type',v),path+'.Adt',reach)
            elif isinstance(v,dict) and set(v)=={'id','generics'}:
                walk(v['id'],owner,path+'.Adt.id',suppress,reach);walk(v['generics'],owner,path+'.Adt.generics',suppress,reach)
            elif isinstance(v,list):
                if path.endswith('.Aggregate[0]') and len(v)==3:walk(v[0],owner,path+'.Adt[0]',suppress,reach)
                elif '.Projection[' in path and '.Field[0]' in path and len(v)==2 and isinstance(v[0],int):pass
                elif '.ptr_metadata.' in path and v==[None,[]]:pass
                else:unknown.append({'path':path,'shape':'Adt-list'})
            elif v!='Builtin':unknown.append({'path':path,'shape':'Adt','value':v})
        if 'Fun' in x:
            v=x['Fun']
            if isinstance(v,dict) and set(v)=={'Regular'} and isinstance(v['Regular'],int):record(owner,('Fun',v['Regular']),path+'.Fun.Regular',reach)
            elif not(isinstance(v,dict) and set(v)=={'Builtin'}):unknown.append({'path':path,'shape':'Fun','value':v})
        if 'Global' in x:
            v=x['Global']
            if isinstance(v,int):record(owner,('Global',v),path+'.Global',reach)
            elif isinstance(v,dict) and isinstance(v.get('id'),int) and 'generics'in v:
                record(owner,('Global',v['id']),path+'.Global.id',reach);walk(v['generics'],owner,path+'.Global.generics',suppress,reach)
            else:unknown.append({'path':path,'shape':'Global','value':v})
        if 'trait_decl_ref' in x:
            q=x['trait_decl_ref']; b=q.get('skip_binder',{}) if isinstance(q,dict) else {};i=b.get('id') if isinstance(b,dict) else None
            if isinstance(i,int):
                target=('TraitDecl',i)
                if target!=suppress:record(owner,target,path+'.trait_decl_ref',reach)
                walk(q.get('regions',[]),owner,path+'.trait_decl_ref.regions',suppress,reach);walk(b.get('generics',{}),owner,path+'.trait_decl_ref.generics',suppress,reach)
            else:unknown.append({'path':path,'shape':'trait_decl_ref'})
        if 'impl_ref' in x:
            q=x['impl_ref']
            if isinstance(q,dict) and isinstance(q.get('id'),int):
                target=('TraitImpl',q['id'])
                if target!=suppress:record(owner,target,path+'.impl_ref',reach)
                walk(q.get('generics',{}),owner,path+'.impl_ref.generics',suppress,reach)
            else:unknown.append({'path':path,'shape':'impl_ref'})
        if 'TraitImpl' in x:
            q=x['TraitImpl']
            if isinstance(q,dict) and isinstance(q.get('id'),int):
                target=('TraitImpl',q['id'])
                if target!=suppress:record(owner,target,path+'.TraitImpl',reach)
                walk(q.get('generics',{}),owner,path+'.TraitImpl.generics',suppress,reach)
            else:unknown.append({'path':path,'shape':'TraitImpl'})
        if 'impl_trait' in x:
            q=x['impl_trait']
            if isinstance(q,dict) and isinstance(q.get('id'),int):
                target=('TraitDecl',q['id'])
                if target!=suppress:record(owner,target,path+'.impl_trait',reach)
                walk(q.get('generics',{}),owner,path+'.impl_trait.generics',suppress,reach)
            else:unknown.append({'path':path,'shape':'impl_trait'})
        if 'TraitMethod' in x:
            q=x['TraitMethod']
            if isinstance(q,list) and len(q)==2 and all(isinstance(z,int) for z in q):
                target=('TraitDecl',q[0])
                if target!=suppress:record(owner,target,path+'.TraitMethod',reach)
            else:unknown.append({'path':path,'shape':'TraitMethod'})
        for k,v in x.items():
            if k in {'Adt','Fun','Global','trait_decl_ref','impl_ref','TraitImpl','impl_trait','TraitMethod'}:continue
            if k=='id' and isinstance(v,int):continue
            walk(v,owner,path+'.'+k,suppress,reach)
    def visit(n):
        if n not in rows:missing.append({'path':'visit','target':list(n)});return
        if n in active:cycles.append([list(x) for x in active[active.index(n):]+[n]]);return
        if n in visited:return
        active.append(n)
        walk(payload(n),n,f'{n[0]}[{n[1]}]',suppressed(rows[n]))
        visited.add(n); active.pop()
        for q in sorted(edges.get(n,set())|reach_only.get(n,set())):visit(q)
    visit(root)
    return {'visited':visited,'edges':edges,'reach_only':reach_only,'cycles':cycles,'missing':missing,'unknown':unknown}

# Find regular-call references to Iterator::zip Fun31 in each selected root's saved body.
def regular_fun_counts(rootid,targetid):
    body=expand(rows[('Fun',rootid)]['body']);out=[]
    def rec(x,path='$'):
        if isinstance(x,dict):
            f=x.get('Fun')
            if isinstance(f,dict) and f.get('Regular')==targetid:out.append(path+'.Fun.Regular')
            for k,v in x.items():rec(v,path+'.'+k)
        elif isinstance(x,list):
            for j,v in enumerate(x):rec(v,f'{path}[{j}]')
    rec(body);return out

zip_calls={str(i):regular_fun_counts(i,31) for i in (0,1)}
reach0=graph_from(('Fun',0)); reach1=graph_from(('Fun',1))
def shortest_path(g,root,target):
    from collections import deque
    q=deque([root]); prev={root:None}
    adj={}
    allpairs=set()
    for owner,deps in g['edges'].items(): allpairs.update((owner,d) for d in deps)
    for owner,deps in g['reach_only'].items(): allpairs.update((owner,d) for d in deps)
    for owner,dep in allpairs: adj.setdefault(owner,set()).add(dep)
    while q:
        n=q.popleft()
        if n==target: break
        for z in sorted(adj.get(n,set())):
            if z not in prev: prev[z]=n;q.append(z)
    if target not in prev:return None
    path=[]; cur=target
    while cur is not None:path.append(cur);cur=prev[cur]
    return list(reversed(path))
# TraitImpl 30 is Iterator for Zip; 43 is a different Zip impl (Destruct).
impl30=expand(rows[('TraitImpl',30)])
zip_impl_details={
 'id':30,'name':name('TraitImpl',30),'span':span('TraitImpl',30),
 'impl_trait_id':impl30.get('impl_trait',{}).get('id'),
 'impl_trait_name':name('TraitDecl',impl30.get('impl_trait',{}).get('id')),
 'generics':impl30.get('generics'),
 'method0_kind':impl30['methods'][0]['kind'],
 'method0_funref_id':impl30['methods'][0]['skip_binder']['id'],
 'method0_funref_name':name('Fun',impl30['methods'][0]['skip_binder']['id']),
 'method0_funref_span':span('Fun',impl30['methods'][0]['skip_binder']['id']),
 'method0_funref_generics_trait_refs':expand(impl30['methods'][0]['skip_binder']['generics']).get('trait_refs'),
 'trait_impl_funref_id':30,
}
impl43=expand(rows[('TraitImpl',43)])
zip_impl_details['neighboring_TraitImpl43_is_different']={'impl_trait_id':impl43.get('impl_trait',{}).get('id'),'impl_trait_name':name('TraitDecl',impl43.get('impl_trait',{}).get('id')),'span':span('TraitImpl',43)}
# Surface only the two source where-clause IDs and source spans from TraitImpl30/Fun32.
zip_impl_details['trait_clause_ids_spans']=[{'clause_id':c['clause_id'],'origin':c['origin'],'span':c['span']['data'],'trait_ref_id':c['trait_']['skip_binder']['id']} for c in impl30['generics']['trait_clauses']]
fun32=expand(rows[('Fun',32)])
zip_impl_details['Fun32_source']=fun32.get('src')
zip_impl_details['Fun32_generics_clause_ids_spans']=[{'clause_id':c['clause_id'],'origin':c['origin'],'span':c['span']['data'],'trait_ref_id':c['trait_']['skip_binder']['id']} for c in fun32.get('generics',{}).get('trait_clauses',[])]
zip_impl_details['Fun32_trait_method_id']=impl30['methods'][0]['kind'].get('TraitMethod')
zip_impl_details['trait_decl0_span']=span('TraitDecl',0)
zip_impl_details['zip_type21_span']=span('Type',21)
trait0=rows[('TraitDecl',0)]
iterator_copied=expand(trait0['methods'][56])
copied_fun_id=iterator_copied['skip_binder']['default']['id']
copied_fun=expand(rows[('Fun',copied_fun_id)])
copied_clause=copied_fun['generics']['trait_clauses'][0]
zip_impl_details['TraitImpl30_method56_mapping']={
 'kind':impl30['methods'][56]['kind'],
 'iterator_trait_method_index':56,
 'iterator_trait_method_name':iterator_copied['skip_binder']['name'],
 'default_funref_id':copied_fun_id,
 'default_funref_name':name('Fun',copied_fun_id),
 'default_funref_span':span('Fun',copied_fun_id),
 'expected_clause_candidate':{'clause_id':copied_clause['clause_id'],'origin':copied_clause['origin'],'span':copied_clause['span']['data'],'trait_decl_id':copied_clause['trait_']['skip_binder']['id'],'trait_args':copied_clause['trait_']['skip_binder']['generics']['types']},
 'actual_impl_trait_ref':impl30['impl_trait'],
 'comparison_note':'Error expected predicate is structurally aligned with Fun35 copied self-bound Iterator<Item=&T>; TraitImpl30 implements Iterator for Zip with Item=(Clause0_Item,Clause1_Item). This records the AST shapes only.'
}

log=LOG.read_text(errors='replace')
start=log.find('error: Type error after transformations:')
err_excerpt='\n'.join(log[start:log.find('\n\n',start)].splitlines()[:20]) if start>=0 else None
report={
 'status':'DIAGNOSTIC_INVENTORY_ONLY','llbc_sha256':H(LLBC),'command_exit_status':json.loads((ROOT/'result.json').read_text())['charon_exit_status'],'has_errors':doc['has_errors'],
 'accepted_as_proof_input':False,
 'error_excerpt':err_excerpt,
 'zip_method_id':31,'zip_method_name':name('Fun',31),'zip_method_span':span('Fun',31),
 'root_zip_call_references':zip_calls,
 'root0_batch_reaches_TraitImpl30':('TraitImpl',30) in reach0['visited'],'root0_reachability_counts':{k:sum(n[0]==k for n in reach0['visited']) for k in COL},
 'root0_missing_refs':reach0['missing'],'root0_missing_non_vtable_refs':[x for x in reach0['missing'] if '.vtable.' not in x['path']],'root0_unknown_shapes':reach0['unknown'],'root0_cycles':reach0['cycles'],
 'root1_try_norm_reaches_TraitImpl30':('TraitImpl',30) in reach1['visited'],'root1_reachability_counts':{k:sum(n[0]==k for n in reach1['visited']) for k in COL},
 'root1_missing_refs':reach1['missing'],'root1_missing_non_vtable_refs':[x for x in reach1['missing'] if '.vtable.' not in x['path']],'root1_unknown_shapes':reach1['unknown'],'root1_cycles':reach1['cycles'],
 'root1_shortest_typed_path_to_TraitImpl30':[{'id':list(n),'name':name(*n)} for n in (shortest_path(reach1,('Fun',1),('TraitImpl',30)) or [])],
 'zip_trait_impl':zip_impl_details,
 'charon_error_source_path':'/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/src/transform/typecheck_and_unify.rs',
 'charon_error_source_location':'lines 280-285 (Mismatched trait clause format)',
 'charon_error_source_hash_sha256':'8f784d2a88f8d7663c7a09da30733dc2f79ef524e4b6699d66cc678cafa94228',
 'charon_error_source_excerpt':'typecheck_and_unify.rs:278-286 formats expected clause and actual trait reference, then reports Mismatched trait clause.',
 'scope':'Mechanical read-only trace of the saved has_errors LLBC and diagnostic. The file is not treated as proof input; no source semantics or repair is asserted.'
}
(HERE/'inventory.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('error_excerpt','zip_trait_impl')},indent=2))
