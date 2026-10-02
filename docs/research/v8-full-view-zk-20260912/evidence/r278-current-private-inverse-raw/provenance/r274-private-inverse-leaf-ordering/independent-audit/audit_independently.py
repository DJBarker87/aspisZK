#!/usr/bin/env python3
"""Independent typed dependency/order audit for the R274 LLBC metadata rewrite."""
import copy, hashlib, json, pathlib
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parent
SRC=ROOT.parent/'r266-private-inverse-leaf-extract/R266PrivateInverseLeaves.llbc'
OUT=ROOT/'R274PrivateInverseLeavesOrdered.llbc'
PIN=ROOT.parent/'r267-private-inverse-leaf-ordering/pinned-reorder_decls.rs'
GEN_AUDIT=ROOT/'audit.json'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
EXPECTED_IN='f4ed281e203e81208acf5c9cbae790d6a15e6ae5c7d5367d21a683768d0bb4a9'
EXPECTED_OUT='fb316e998775a411073d19667a06a15647af4cc9599188d7061596259b211768'
EXPECTED_PIN='8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632'
assert H(SRC)==EXPECTED_IN and H(OUT)==EXPECTED_OUT and H(PIN)==EXPECTED_PIN
src_doc=json.loads(SRC.read_text()); out_doc=json.loads(OUT.read_text())
assert src_doc['has_errors'] is False and src_doc['translated']['ordered_decls']==[]
# The serializer-level preservation check includes declaration tables, source
# metadata, file/item-name tables, hash-cons wrappers and all other JSON fields.
a=copy.deepcopy(src_doc); b=copy.deepcopy(out_doc)
a['translated'].pop('ordered_decls'); b['translated'].pop('ordered_decls')
assert a==b

GROUPS={'Type':'type_decls','Fun':'fun_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}
rows={(kind,row['def_id']):row for kind,key in GROUPS.items() for row in src_doc['translated'][key] if isinstance(row,dict) and isinstance(row.get('def_id'),int)}
roots=[('Fun',0),('Fun',1)]
for root in roots:
    assert root in rows
    row=rows[root]
    assert row.get('body') not in (None,'Opaque')
    assert row.get('item_meta',{}).get('is_local') is True

# Decode Charon's shared JSON nodes so nested references are seen uniformly.
shared={}
def index_shared(x):
    if isinstance(x,dict):
        if set(x)=={'HashConsedValue'}:
            ident,value=x['HashConsedValue']
            assert ident not in shared or shared[ident]==value
            shared[ident]=value
        for v in x.values(): index_shared(v)
    elif isinstance(x,list):
        for v in x: index_shared(v)
index_shared(src_doc)
def expand(x, stack=()):
    if isinstance(x,dict):
        if set(x)=={'HashConsedValue'}:
            i,v=x['HashConsedValue']; assert i not in stack
            return expand(v,stack+(i,))
        if set(x)=={'Deduplicated'}:
            i=x['Deduplicated']; assert i in shared and i not in stack
            return expand(shared[i],stack+(i,))
        return {k:expand(v,stack) for k,v in x.items()}
    if isinstance(x,list): return [expand(v,stack) for v in x]
    return x

labels={}
for entry in src_doc['translated'].get('item_names',[]):
    key=entry.get('key',{})
    if len(key)==1:
        kind,ident=next(iter(key.items()))
        name='::'.join(part.get('Ident',['?'])[0] if isinstance(part,dict) and 'Ident' in part else str(part) for part in entry.get('value',[]))
        labels[(kind,ident)]=name

edges=set(); typed=[]; missing=[]; skipped=[]; unknown=[]; reached_defaults=[]; reach_only={}
ALLOWLIST={
 ('TraitDecl',0,'TraitDecl[0].vtable.id.Adt',('Type',5),'core::iter::traits::iterator::Iterator::{vtable}'),
 ('TraitDecl',19,'TraitDecl[19].vtable.id.Adt',('Type',43),'core::cmp::PartialOrd::{vtable}'),
 ('TraitDecl',20,'TraitDecl[20].vtable.id.Adt',('Type',44),'core::cmp::PartialEq::{vtable}'),
}
def record(owner,target,path):
    typed.append({'owner':list(owner),'path':path,'target':list(target)})
    if target not in rows:
        key=(owner[0],owner[1],path,target,labels.get(target))
        if (key in ALLOWLIST and owner[0] in ('TraitDecl','TraitImpl')
                and target[0]=='Type' and '.vtable.id' in path
                and path.startswith(f'{owner[0]}[{owner[1]}].vtable.')
                and isinstance(labels.get(target),str) and labels[target].endswith('::{vtable}')):
            skipped.append({'owner':list(owner),'path':path,'target':list(target),'item_label':labels.get(target),'kind':'vtable metadata absent row'})
            return
        missing.append({'owner':list(owner),'path':path,'target':list(target),'item_label':labels.get(target)})
        return
    edges.add((owner,target))
def enqueue_only(owner,target,path):
    # Pinned Charon TraitDecl default IDs use insert_node: they are reachable,
    # but are not dependency edges used to order the default before its trait.
    typed.append({'owner':list(owner),'path':path,'target':list(target),'edge':False})
    if target not in rows:
        missing.append({'owner':list(owner),'path':path,'target':list(target),'relation':'pinned insert_node'})
    else:
        reach_only.setdefault(owner,set()).add(target)

def walk(x,owner,path,suppress):
    if isinstance(x,list):
        for i,v in enumerate(x): walk(v,owner,f'{path}[{i}]',suppress)
        return
    if not isinstance(x,dict): return
    # LLBC typed references: process each explicit constructor; arbitrary integer
    # IDs are deliberately ignored unless nested under one of these constructors.
    if 'Adt' in x:
        v=x['Adt']
        if isinstance(v,int): record(owner,('Type',v),path+'.Adt')
        elif isinstance(v,dict) and set(v)=={'id','generics'}:
            walk(v['id'],owner,path+'.Adt.id',suppress); walk(v['generics'],owner,path+'.Adt.generics',suppress)
        elif isinstance(v,list):
            if path.endswith('.Aggregate[0]') and len(v)==3:
                walk(v[0],owner,path+'.Adt[0]',suppress)
            elif '.Projection[' in path and '.Field[0]' in path and len(v)==2 and isinstance(v[0],int):
                pass
            elif '.ptr_metadata.' in path and v==[None,[]]:
                pass
            else: unknown.append({'path':path,'shape':'Adt-list','value':v})
        elif v!='Builtin': unknown.append({'path':path,'shape':'Adt','value':v})
    if 'Fun' in x:
        v=x['Fun']
        if isinstance(v,dict) and set(v)=={'Regular'} and isinstance(v['Regular'],int): record(owner,('Fun',v['Regular']),path+'.Fun.Regular')
        elif not (isinstance(v,dict) and set(v)=={'Builtin'}): unknown.append({'path':path,'shape':'Fun','value':v})
    if 'Global' in x:
        v=x['Global']
        if isinstance(v,int): record(owner,('Global',v),path+'.Global')
        elif isinstance(v,dict) and isinstance(v.get('id'),int) and 'generics' in v:
            record(owner,('Global',v['id']),path+'.Global.id'); walk(v['generics'],owner,path+'.Global.generics',suppress)
        else: unknown.append({'path':path,'shape':'Global','value':v})
    if 'trait_decl_ref' in x:
        v=x['trait_decl_ref']; binder=v.get('skip_binder',{}) if isinstance(v,dict) else {}
        ident=binder.get('id') if isinstance(binder,dict) else None
        if isinstance(ident,int):
            target=('TraitDecl',ident)
            if target!=suppress: record(owner,target,path+'.trait_decl_ref')
            walk(v.get('regions',[]),owner,path+'.trait_decl_ref.regions',suppress)
            walk(binder.get('generics',{}),owner,path+'.trait_decl_ref.generics',suppress)
        else: unknown.append({'path':path,'shape':'trait_decl_ref','value':v})
    if 'impl_ref' in x:
        v=x['impl_ref']
        if isinstance(v,dict) and isinstance(v.get('id'),int):
            target=('TraitImpl',v['id'])
            if target!=suppress: record(owner,target,path+'.impl_ref')
            walk(v.get('generics',{}),owner,path+'.impl_ref.generics',suppress)
        else: unknown.append({'path':path,'shape':'impl_ref','value':v})
    if 'TraitImpl' in x:
        v=x['TraitImpl']
        if isinstance(v,dict) and isinstance(v.get('id'),int):
            target=('TraitImpl',v['id'])
            if target!=suppress: record(owner,target,path+'.TraitImpl')
            walk(v.get('generics',{}),owner,path+'.TraitImpl.generics',suppress)
        else: unknown.append({'path':path,'shape':'TraitImpl','value':v})
    if 'impl_trait' in x:
        v=x['impl_trait']
        if isinstance(v,dict) and isinstance(v.get('id'),int):
            target=('TraitDecl',v['id'])
            if target!=suppress: record(owner,target,path+'.impl_trait')
            walk(v.get('generics',{}),owner,path+'.impl_trait.generics',suppress)
        else: unknown.append({'path':path,'shape':'impl_trait','value':v})
    if 'TraitMethod' in x:
        v=x['TraitMethod']
        if isinstance(v,list) and len(v)==2 and all(isinstance(q,int) for q in v):
            target=('TraitDecl',v[0])
            if target!=suppress: record(owner,target,path+'.TraitMethod')
        else: unknown.append({'path':path,'shape':'TraitMethod','value':v})
    consumed={'Adt','Fun','Global','trait_decl_ref','impl_ref','TraitImpl','impl_trait','TraitMethod'}
    for k,v in x.items():
        if k in consumed or (k=='id' and isinstance(v,int)): continue
        walk(v,owner,path+'.'+k,suppress)

def parent_suppression(row):
    source=expand(row.get('src'))
    if not isinstance(source,dict): return None
    if 'TraitImpl' in source:
        ident=source['TraitImpl'].get('impl_ref',{}).get('id')
        return ('TraitImpl',ident) if isinstance(ident,int) else None
    if 'TraitDecl' in source:
        ident=source['TraitDecl'].get('trait_ref',{}).get('id')
        return ('TraitDecl',ident) if isinstance(ident,int) else None
    return None

def visit_payload(owner):
    row=expand(rows[owner])
    if owner[0]=='Fun':
        fields={k:row[k] for k in ('generics','signature','body')}
        src=row.get('src')
        if isinstance(src,dict) and 'TraitDecl' in src:
            ident=src['TraitDecl'].get('trait_ref',{}).get('id')
            if isinstance(ident,int):
                t=('TraitDecl',ident)
                if t!=owner: record(owner,t,f'Fun[{owner[1]}].src.TraitDecl.trait_ref')
        return fields
    if owner[0]=='TraitDecl':
        fields={k:row[k] for k in ('generics','implied_clauses','types','vtable')}
        for i,c in enumerate(row.get('consts',[])):
            fields[f'const[{i}].ty']=c['ty']
            if c.get('default') is not None:
                g=c['default']; target=('Global',g['id']); reached_defaults.append([list(owner),'const',i,list(target)])
                enqueue_only(owner,target,f'TraitDecl[{owner[1]}].const[{i}].default')
                fields[f'const[{i}].default.generics']=g.get('generics',{})
        for i,m in enumerate(row.get('methods',[])):
            if m is None: continue
            fields[f'method[{i}].params']=m['params']; fields[f'method[{i}].signature']=m['skip_binder']['signature']
            if m['skip_binder'].get('default') is not None:
                f=m['skip_binder']['default']; target=('Fun',f['id']); reached_defaults.append([list(owner),'method',i,list(target)])
                enqueue_only(owner,target,f'TraitDecl[{owner[1]}].method[{i}].default')
                fields[f'method[{i}].default.generics']=f.get('generics',{})
        return fields
    return {k:v for k,v in row.items() if k not in ('def_id','item_meta','src','is_global_initializer')}

visited=set(); active=[]; graph={}; cycles=[]
def visit(node):
    if node not in rows: missing.append({'owner':list(active[-1]) if active else None,'path':'DFS node','target':list(node)}); return
    if node in active:
        cycles.append([list(x) for x in active[active.index(node):]+[node]]); return
    if node in visited: return
    active.append(node)
    walk(visit_payload(node),node,f'{node[0]}[{node[1]}]',parent_suppression(rows[node]))
    deps={b for a,b in edges if a==node}; graph[node]=deps
    for dep in sorted(deps | reach_only.get(node,set())): visit(dep)
    active.pop(); visited.add(node)
for root in roots: visit(root)
assert not missing, missing
assert not unknown, unknown
assert not cycles, cycles
expected_skips={(('TraitDecl',0),'TraitDecl[0].vtable.id.Adt',('Type',5)),(('TraitDecl',19),'TraitDecl[19].vtable.id.Adt',('Type',43)),(('TraitDecl',20),'TraitDecl[20].vtable.id.Adt',('Type',44))}
actual_skips={(tuple(s['owner']),s['path'],tuple(s['target'])) for s in skipped}
assert actual_skips==expected_skips, (actual_skips,expected_skips)

# Check declared order as a dependency-before-user topological ordering.
ordered=[]
for entry in out_doc['translated']['ordered_decls']:
    assert isinstance(entry,dict) and len(entry)==1
    kind,group=next(iter(entry.items()))
    assert isinstance(group,dict) and set(group)=={'NonRec'} and isinstance(group['NonRec'],int)
    ordered.append((kind,group['NonRec']))
assert len(ordered)==len(set(ordered)) and set(ordered)==visited
pos={n:i for i,n in enumerate(ordered)}
assert all(pos[dep]<pos[user] for user,deps in graph.items() for dep in deps)

# Independently validate retained generator audit counters/edges and each
# recorded missing-vtable item label against input item_names.
generator_src=(ROOT/'order_metadata.py').read_text()
assert 'PINNED_SHA = "8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632"' in generator_src
assert 'target[0] == "Type"' in generator_src and 'item_label.endswith("::{vtable}")' in generator_src
gen=json.loads(GEN_AUDIT.read_text())
edge_set={(a,b) for a,b in edges}
assert edge_set=={(tuple(e['from']),tuple(e['to'])) for e in gen['dependency_edges']}
assert len(typed)==len(gen['typed_reference_census'])==309
assert len(edge_set)==len(gen['dependency_edges'])==54
assert gen['cycles']==[] and gen['unknown_reference_shapes']==[] and gen['all_refs_present'] is True
for s in skipped:
    target=tuple(s['target'])
    assert s['item_label']==labels.get(target)
    assert s['kind']=='vtable metadata absent row'

report={
 'status':'PASS_INDEPENDENT_STRUCTURAL_AUDIT','input_sha256':H(SRC),'output_sha256':H(OUT),'pinned_reorder_sha256':H(PIN),
 'roots':[list(n) for n in roots],'reachable_counts':{k:sum(n[0]==k for n in visited) for k in GROUPS},
 'ordered_declaration_count':len(ordered),'dependency_edge_count':len(edge_set),'typed_reference_occurrence_count':len(typed),
 'input_output_equal_except_ordered_decls':True,'all_reachable_once_no_extras':True,
 'all_dependencies_precede_users':True,'cycles':cycles,'unknown_typed_reference_shapes':unknown,
 'missing_non_vtable_references':missing,'skipped_absent_vtable_metadata':skipped,
 'only_three_vtable_skips_match_allowlist':actual_skips==expected_skips,
 'pinned_trait_default_relations_seen':len(reached_defaults),
 'default_dependency_rule':'Pinned Charon uses insert_node (reachability only, not a dependency edge) for trait default function/constant IDs; no such defaults are present in this reachable closure.',
 'current_generator_skip_guard':'current order_metadata.py checks source kind, vtable path, Type target, and item label ending in {vtable}; the pinned source hash is checked in full. Independent audit additionally restricts this input to the exact three observed owner/path/Type/label tuples.',
 'generator_edge_set_matches_independent_edge_set':True,'generator_counts_match':True,
 'scope':'Structural LLBC metadata audit only; no translation or semantic theorem is established.'}
(HERE/'independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
