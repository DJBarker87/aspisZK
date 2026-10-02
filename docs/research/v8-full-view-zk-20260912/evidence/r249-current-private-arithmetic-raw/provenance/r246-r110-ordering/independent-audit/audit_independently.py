"""Independent structural audit of R246 metadata-only LLBC ordering repair."""
import copy,hashlib,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent; ROOT=HERE.parent
SRC=ROOT.parent/'r245-r110-leaf-extract/R245R110Leaves.llbc'; OUT=ROOT/'R246R110Ordered.llbc'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(SRC)=='59412a374a2753759103071c7190ac6587249517b0f991e619afc8a12a93e197'
assert H(OUT)=='83cb3e55a865bb66c2003ac670a9f6adcc7584ca600f468dab05a700ab98aab9'
a,b=(json.loads(p.read_text()) for p in (SRC,OUT))
assert a['has_errors'] is False and a['translated']['ordered_decls']==[]
x=copy.deepcopy(a); y=copy.deepcopy(b); x['translated'].pop('ordered_decls'); y['translated'].pop('ordered_decls'); assert x==y
# Decode hashconsed values independently before following typed IDs.
tab={}
def collect(o):
    if isinstance(o,dict):
        if set(o)=={'HashConsedValue'}:
            i,v=o['HashConsedValue']; assert i not in tab or tab[i]==v; tab[i]=v
        for v in o.values(): collect(v)
    elif isinstance(o,list):
        for v in o: collect(v)
collect(a)
def expand(o,stack=()):
    if isinstance(o,dict):
        if set(o)=={'HashConsedValue'}:
            i,v=o['HashConsedValue']; assert i not in stack; return expand(v,stack+(i,))
        if set(o)=={'Deduplicated'}:
            i=o['Deduplicated']; assert i in tab and i not in stack; return expand(tab[i],stack+(i,))
        return {k:expand(v,stack) for k,v in o.items()}
    if isinstance(o,list): return [expand(v,stack) for v in o]
    return o
fields={'Type':'type_decls','Fun':'fun_decls','Global':'global_decls'}
allfields={**fields,'TraitDecl':'trait_decls','TraitImpl':'trait_impls'}
rows={(k,r['def_id']):r for k,f in allfields.items() for r in a['translated'][f] if isinstance(r,dict) and isinstance(r.get('def_id'),int)}
roots=[('Fun',i) for i in [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16]]
for n in roots: assert rows[n]['item_meta']['is_local'] and isinstance(rows[n].get('body'),dict)
assert ('Fun',6) in rows
fun6=expand(rows[('Fun',6)])
assert isinstance(fun6.get('body'),dict) and fun6.get('item_meta',{}).get('is_local') is True
assert 'input' in json.dumps(fun6.get('item_meta',{}).get('name'))
def payload(n):
    r=expand(rows[n]); return {k:v for k,v in r.items() if k not in {'def_id','item_meta','src','is_global_initializer'}}
graph={}; shapes={}; traits=[]; idrows=[]
def scan(o,path,n,refs,occ):
    if isinstance(o,dict):
        if 'Adt' in o:
            v=o['Adt']
            if isinstance(v,int): i=v; tag='Adt-id'
            elif isinstance(v,dict) and isinstance(v.get('id'),int): i=v['id']; tag='Adt-record-id'
            else:i=None
            if i is not None: refs.add(('Type',i)); occ.append((n,'Type',i,path+'.Adt')); shapes[tag]=shapes.get(tag,0)+1
        if 'Fun' in o:
            v=o['Fun']
            if isinstance(v,dict) and set(v)=={'Regular'} and isinstance(v['Regular'],int):
                i=v['Regular'];refs.add(('Fun',i));occ.append((n,'Fun',i,path+'.Fun.Regular'));shapes['Fun.Regular']=shapes.get('Fun.Regular',0)+1
            elif isinstance(v,dict) and set(v)=={'Builtin'}:shapes['Fun.Builtin']=shapes.get('Fun.Builtin',0)+1
            else:raise AssertionError(('unclassified Fun tag',n,path,v))
        if 'Global' in o:
            v=o['Global']
            if isinstance(v,int):i=v;tag='Global.int'
            elif isinstance(v,dict) and isinstance(v.get('id'),int) and 'generics'in v:i=v['id'];tag='Global.record'
            else:raise AssertionError(('unclassified Global ref',n,path,v))
            refs.add(('Global',i));occ.append((n,'Global',i,path+'.Global'));shapes[tag]=shapes.get(tag,0)+1
        for key in ('TraitDecl','TraitImpl','TraitMethod','trait_ref','impl_ref','impl_trait'):
            if key in o:traits.append((n,path+'.'+key))
        if isinstance(o.get('id'),int):idrows.append({'owner':list(n),'path':path,'id':o['id'],'keys':sorted(o)})
        for k,v in o.items():scan(v,path+'.'+k,n,refs,occ)
    elif isinstance(o,list):
        for j,v in enumerate(o):scan(v,f'{path}[{j}]',n,refs,occ)
visited=set();active=[];post=[];occ=[]
def visit(n):
    if n not in rows:raise AssertionError(('missing typed declaration',n,active[-1] if active else None))
    if n in active:raise AssertionError(('dependency cycle',active[active.index(n):]+[n]))
    if n in visited:return
    active.append(n); refs=set();scan(payload(n),f'{n[0]}[{n[1]}]',n,refs,occ);graph[n]=refs
    for dep in sorted(refs):visit(dep)
    active.pop();visited.add(n);post.append(n)
for n in roots:visit(n)
assert not traits,traits
# Charon has an explicit Fun ItemSource::TraitDecl edge beyond AST visiting.
fun_trait_sources=[]
for n in visited:
    if n[0]=='Fun':
        s=expand(rows[n]).get('src')
        if isinstance(s,dict) and 'TraitDecl' in s:fun_trait_sources.append((n,s['TraitDecl']))
assert not fun_trait_sources,fun_trait_sources
ordered=[]
for g in b['translated']['ordered_decls']:
    assert isinstance(g,dict) and len(g)==1
    k,w=next(iter(g.items()));assert isinstance(w,dict) and set(w)=={'NonRec'}
    ordered.append((k,w['NonRec']))
assert len(ordered)==len(set(ordered)) and set(ordered)==visited
assert ('Fun',6) not in ordered and ('Fun',6) not in visited
position={n:i for i,n in enumerate(ordered)}
assert all(position[d]<position[n] for n,ds in graph.items() for d in ds)
# All declarations, including excluded Fun6, are byte-for-byte unchanged.
for k,f in allfields.items():
    old={r['def_id']:r for r in a['translated'][f] if isinstance(r,dict) and 'def_id'in r}
    new={r['def_id']:r for r in b['translated'][f] if isinstance(r,dict) and 'def_id'in r}
    assert old==new
edges={(n,d) for n,ds in graph.items() for d in ds}
gen=json.loads((ROOT/'audit.json').read_text())
assert edges=={(tuple(e['from']),tuple(e['to'])) for e in gen['edges']}
def tail(path):return path.split('.',1)[1] if '.' in path else ''
assert {(tail(x['path']),x['id'],tuple(x['keys'])) for x in idrows}=={(tail(x['path']),x['id'],tuple(x['keys'])) for x in gen['integer_id_census']}
report={'status':'PASS_INDEPENDENT_STRUCTURAL_AUDIT','input_sha256':H(SRC),'output_sha256':H(OUT),'roots':[list(n) for n in roots],'reachable_counts':{k:sum(n[0]==k for n in visited) for k in fields},'ordered_count':len(ordered),'edge_count':len(edges),'edge_set_matches_generator':True,'typed_reference_shapes':shapes,'integer_id_dictionary_count':len(idrows),'integer_id_census_matches_generator':True,'missing_refs':[],'cycles':[],'trait_ast_refs':[],'fun_trait_source_refs':[],'all_dependencies_before_users':True,'all_reachable_exactly_once_no_extras':True,'all_type_fun_global_trait_declaration_rows_identical':True,'only_changed_json_path':'translated.ordered_decls','all_other_json_identical':True,'fun6_input_present_unchanged':True,'fun6_input_emitted_or_reached':False,'cinput_scope':'Fun6 C::input remains present in the original declaration table, unchanged, but is not a root, not reachable from selected roots, and not emitted. The existing README marks it excluded/unproved because of Option try-trait dictionaries.','scope':'Structural metadata-order audit only; no translation or source-semantics claim.','typed_reference_occurrences':[{'owner':list(n),'kind':k,'id':i,'path':p} for n,k,i,p in occ],'integer_id_dictionaries':idrows,'edges':[{'from':list(n),'to':list(d)} for n,d in sorted(edges)]}
report['root_body_metadata']=[{'kind':k,'id':i,'local':rows[(k,i)]['item_meta']['is_local'],'has_body':isinstance(rows[(k,i)].get('body'),dict),'name_metadata':expand(rows[(k,i)]).get('item_meta',{}).get('name')} for k,i in roots]
(HERE/'independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in {'typed_reference_occurrences','integer_id_dictionaries','edges'}},indent=2))
