"""Independent structural audit of R255 complete Fun0..16 LLBC ordering."""
import copy,hashlib,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parent
SRC=ROOT.parent/'r245-r110-leaf-extract/R245R110Leaves.llbc';OUT=ROOT/'R255R110CompleteOrdered.llbc'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(SRC)=='59412a374a2753759103071c7190ac6587249517b0f991e619afc8a12a93e197'
assert H(OUT)=='65d240e27115591fa6dc459e9c4a94785667840cbf1f1deddafc892c764dca88'
a,b=(json.loads(p.read_text()) for p in (SRC,OUT))
assert a['has_errors'] is False and a['translated']['ordered_decls']==[]
x=copy.deepcopy(a);y=copy.deepcopy(b);x['translated'].pop('ordered_decls');y['translated'].pop('ordered_decls');assert x==y
# Decode the file-level hash-cons table without using the production generator.
tab={}
def collect(o):
    if isinstance(o,dict):
        if set(o)=={'HashConsedValue'}:
            i,v=o['HashConsedValue'];assert i not in tab or tab[i]==v;tab[i]=v
        for v in o.values():collect(v)
    elif isinstance(o,list):
        for v in o:collect(v)
collect(a)
def expand(o,stack=()):
    if isinstance(o,dict):
        if set(o)=={'HashConsedValue'}:
            i,v=o['HashConsedValue'];assert i not in stack;return expand(v,stack+(i,))
        if set(o)=={'Deduplicated'}:
            i=o['Deduplicated'];assert i in tab and i not in stack;return expand(tab[i],stack+(i,))
        return {k:expand(v,stack) for k,v in o.items()}
    if isinstance(o,list):return [expand(v,stack) for v in o]
    return o
fields={'Type':'type_decls','Fun':'fun_decls','Global':'global_decls'}
allfields={**fields,'TraitDecl':'trait_decls','TraitImpl':'trait_impls'}
rows={(k,r['def_id']):r for k,f in allfields.items() for r in a['translated'][f] if isinstance(r,dict) and isinstance(r.get('def_id'),int)}
roots=[('Fun',i) for i in range(17)]
for n in roots:assert n in rows and rows[n]['item_meta']['is_local'] and isinstance(rows[n].get('body'),dict)
fun6=expand(rows[('Fun',6)])
assert 'input' in json.dumps(fun6.get('item_meta',{}).get('name'))
def payload(n):
    r=expand(rows[n]);return {k:v for k,v in r.items() if k not in {'def_id','item_meta','src','is_global_initializer'}}
graph={};shapes={};traits=[];idrows=[];occ=[]
def scan(o,path,n,refs):
    if isinstance(o,dict):
        if 'Adt' in o:
            v=o['Adt']
            if isinstance(v,int):i=v;tag='Adt-id'
            elif isinstance(v,dict) and isinstance(v.get('id'),int):i=v['id'];tag='Adt-record-id'
            else:i=None
            if i is not None:refs.add(('Type',i));occ.append({'owner':list(n),'kind':'Type','id':i,'path':path+'.Adt'});shapes[tag]=shapes.get(tag,0)+1
        if 'Fun' in o:
            v=o['Fun']
            if isinstance(v,dict) and set(v)=={'Regular'} and isinstance(v['Regular'],int):
                i=v['Regular'];refs.add(('Fun',i));occ.append({'owner':list(n),'kind':'Fun','id':i,'path':path+'.Fun.Regular'});shapes['Fun.Regular']=shapes.get('Fun.Regular',0)+1
            elif isinstance(v,dict) and set(v)=={'Builtin'}:shapes['Fun.Builtin']=shapes.get('Fun.Builtin',0)+1
            else:raise AssertionError(('unclassified Fun reference',n,path,v))
        if 'Global' in o:
            v=o['Global']
            if isinstance(v,int):i=v;tag='Global.int'
            elif isinstance(v,dict) and isinstance(v.get('id'),int) and 'generics' in v:i=v['id'];tag='Global.record'
            else:raise AssertionError(('unclassified Global ref',n,path,v))
            refs.add(('Global',i));occ.append({'owner':list(n),'kind':'Global','id':i,'path':path+'.Global'});shapes[tag]=shapes.get(tag,0)+1
        for key in ('TraitDecl','TraitImpl','TraitMethod','trait_ref','impl_ref','impl_trait'):
            if key in o:traits.append({'owner':list(n),'path':path+'.'+key,'value':o[key]})
        if isinstance(o.get('id'),int):idrows.append({'owner':list(n),'path':path,'id':o['id'],'keys':sorted(o)})
        for k,v in o.items():scan(v,path+'.'+k,n,refs)
    elif isinstance(o,list):
        for j,v in enumerate(o):scan(v,f'{path}[{j}]',n,refs)
visited=set();active=[];post=[]
def visit(n):
    if n not in rows:raise AssertionError(('unresolved typed declaration',n,active[-1] if active else None))
    if n in active:raise AssertionError(('cycle',active[active.index(n):]+[n]))
    if n in visited:return
    active.append(n);refs=set();scan(payload(n),f'{n[0]}[{n[1]}]',n,refs);graph[n]=refs
    for d in sorted(refs):visit(d)
    active.pop();visited.add(n);post.append(n)
for n in roots:visit(n)
assert not traits,traits
# Pinned Charon ReorderDeps also records this special Fun source edge; detect it separately.
trait_sources=[]
for n in visited:
    if n[0]=='Fun':
        s=expand(rows[n]).get('src')
        if isinstance(s,dict) and 'TraitDecl' in s:trait_sources.append({'owner':list(n),'source':s['TraitDecl']})
assert not trait_sources,trait_sources
ordered=[]
for group in b['translated']['ordered_decls']:
    assert isinstance(group,dict) and len(group)==1
    k,v=next(iter(group.items()));assert isinstance(v,dict) and set(v)=={'NonRec'}
    ordered.append((k,v['NonRec']))
assert len(ordered)==len(set(ordered)) and set(ordered)==visited
pos={n:i for i,n in enumerate(ordered)}
assert all(pos[d]<pos[n] for n,ds in graph.items() for d in ds)
for k,f in allfields.items():
    old={r['def_id']:r for r in a['translated'][f] if isinstance(r,dict) and 'def_id' in r}
    new={r['def_id']:r for r in b['translated'][f] if isinstance(r,dict) and 'def_id' in r}
    assert old==new
edges={(n,d) for n,ds in graph.items() for d in ds}
gen=json.loads((ROOT/'audit.json').read_text())
assert edges=={(tuple(e['from']),tuple(e['to'])) for e in gen['edges']}
def suffix(p):return p.split('.',1)[1] if '.' in p else ''
assert {(suffix(x['path']),x['id'],tuple(x['keys'])) for x in idrows}=={(suffix(x['path']),x['id'],tuple(x['keys'])) for x in gen['integer_id_census']}
def short_name(meta):
    name=meta.get('name')
    if isinstance(name,list) and name and isinstance(name[-1],dict) and 'Ident' in name[-1]:return name[-1]['Ident'][0]
    return None
root_metadata=[{'id':i,'local':rows[('Fun',i)]['item_meta']['is_local'],'has_body':isinstance(rows[('Fun',i)].get('body'),dict),'terminal_name':short_name(expand(rows[('Fun',i)]).get('item_meta',{}))} for i in range(17)]
report={'status':'PASS_INDEPENDENT_STRUCTURAL_AUDIT','input_sha256':H(SRC),'output_sha256':H(OUT),'roots':[list(n) for n in roots],'root_body_metadata':root_metadata,'reachable_counts':{k:sum(n[0]==k for n in visited) for k in fields},'ordered_count':len(ordered),'edge_count':len(edges),'edge_set_matches_generator':True,'typed_reference_shapes':shapes,'integer_id_dictionary_count':len(idrows),'integer_id_census_matches_generator':True,'missing_refs':[],'cycles':[],'trait_ast_refs':traits,'fun_trait_source_refs':trait_sources,'all_dependencies_before_users':True,'all_reachable_exactly_once_no_extras':True,'all_type_fun_global_trait_rows_identical':True,'only_changed_json_path':'translated.ordered_decls','all_other_json_identical':True,'fun6_input_included_as_root':True,'scope':'Structural metadata order audit only; no translation or source-semantics claim.','typed_reference_occurrences':occ,'integer_id_dictionaries':idrows,'edges':[{'from':list(u),'to':list(v)} for u,v in sorted(edges)]}
(HERE/'independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in {'typed_reference_occurrences','integer_id_dictionaries','edges'}},indent=2))
