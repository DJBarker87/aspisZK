"""Independent structural audit of R237 declaration ordering; no translation."""
import copy, hashlib, json, pathlib
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parent
SRC=ROOT.parent/'r231-coefficient-extract/R231NormLeaves.llbc'
OUT=ROOT/'R237CoeffOrdered.llbc'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(SRC)=='ab72ee9cb72ec543bc8a86f5fc2a627cd3c5847eeed46c049d78ab25182294f8'
assert H(OUT)=='d4fa8045d5b43c2fa5930b201417a0e6a683c9c783030dcc4c0b3ffbb95d9d3c'
a,b=(json.loads(p.read_text()) for p in (SRC,OUT))
assert a['has_errors'] is False and a['translated']['ordered_decls']==[]
x=copy.deepcopy(a); y=copy.deepcopy(b)
x['translated'].pop('ordered_decls'); y['translated'].pop('ordered_decls')
assert x==y
# Expand the global hash-cons table before following typed references.
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
rows={(k,r['def_id']):r for k,f in fields.items() for r in a['translated'][f] if isinstance(r,dict) and isinstance(r.get('def_id'),int)}
roots=[('Fun',i) for i in range(4)]
for n in roots:
    assert rows[n]['item_meta']['is_local'] and isinstance(rows[n]['body'],dict)
def payload(n):
    r=expand(rows[n]); return {k:v for k,v in r.items() if k not in {'def_id','item_meta','src','is_global_initializer'}}
# These are the typed reference constructors visited by Charon's DepsForItem:
# TypeId in ADT, regular function id, and global id (direct or generic record).
graph={}; shapes={}; trait_refs=[]; integer_id_rows=[]
def scan(o,path,n,refs,occ):
    if isinstance(o,dict):
        if 'Adt' in o:
            v=o['Adt']
            if isinstance(v,int): i=v; tag='Adt-id'
            elif isinstance(v,dict) and isinstance(v.get('id'),int): i=v['id']; tag='Adt-record-id'
            else: i=None
            if i is not None: refs.add(('Type',i)); occ.append((n,'Type',i,path+'.Adt')); shapes[tag]=shapes.get(tag,0)+1
        if 'Fun' in o:
            v=o['Fun']
            if isinstance(v,dict) and set(v)=={'Regular'} and isinstance(v['Regular'],int):
                i=v['Regular']; refs.add(('Fun',i)); occ.append((n,'Fun',i,path+'.Fun.Regular')); shapes['Fun.Regular']=shapes.get('Fun.Regular',0)+1
            elif isinstance(v,dict) and set(v)=={'Builtin'}: shapes['Fun.Builtin']=shapes.get('Fun.Builtin',0)+1
            else: raise AssertionError(('unknown Fun reference',n,path,v))
        if 'Global' in o:
            v=o['Global']
            if isinstance(v,int): i=v
            elif isinstance(v,dict) and isinstance(v.get('id'),int) and 'generics' in v: i=v['id']
            else: raise AssertionError(('unknown Global reference',n,path,v))
            refs.add(('Global',i)); occ.append((n,'Global',i,path+'.Global'))
            tag='Global.int' if isinstance(v,int) else 'Global.record'; shapes[tag]=shapes.get(tag,0)+1
        for key in ('TraitDecl','TraitImpl','TraitMethod','trait_ref','impl_ref','impl_trait'):
            if key in o: trait_refs.append((n,path+'.'+key))
        if isinstance(o.get('id'),int):
            integer_id_rows.append({'owner':list(n),'path':path,'id':o['id'],'keys':sorted(o)})
        for k,v in o.items(): scan(v,path+'.'+k,n,refs,occ)
    elif isinstance(o,list):
        for i,v in enumerate(o): scan(v,f'{path}[{i}]',n,refs,occ)
visited=set(); stack=[]; post=[]; occ=[]
def visit(n):
    if n not in rows: raise AssertionError(('unresolved typed reference',n,stack[-1] if stack else None))
    if n in stack: raise AssertionError(('cycle',stack[stack.index(n):]+[n]))
    if n in visited: return
    stack.append(n); refs=set(); scan(payload(n),f'{n[0]}[{n[1]}]',n,refs,occ); graph[n]=refs
    for d in sorted(refs): visit(d)
    stack.pop(); visited.add(n); post.append(n)
for n in roots: visit(n)
assert not trait_refs
# Charon's reorder pass adds an explicit edge for Fun ItemSource::TraitDecl.
# That edge is outside the regular AST traversal, so audit it separately.
trait_source_refs=[]
for n in visited:
    if n[0]=='Fun':
        source=expand(rows[n]).get('src')
        if isinstance(source,dict) and 'TraitDecl' in source:
            trait_source_refs.append((n,source['TraitDecl']))
assert not trait_source_refs
ordered=[]
for g in b['translated']['ordered_decls']:
    assert isinstance(g,dict) and len(g)==1
    k,v=next(iter(g.items())); assert isinstance(v,dict) and set(v)=={'NonRec'}
    ordered.append((k,v['NonRec']))
assert len(ordered)==len(set(ordered)) and set(ordered)==visited
pos={n:i for i,n in enumerate(ordered)}
assert all(pos[d]<pos[n] for n,ds in graph.items() for d in ds)
# Verify every translated type/fun/global row is unchanged in its source encoding.
for k,f in fields.items():
    old={r['def_id']:r for r in a['translated'][f] if isinstance(r,dict) and 'def_id' in r}
    new={r['def_id']:r for r in b['translated'][f] if isinstance(r,dict) and 'def_id' in r}
    assert old==new
edges={(u,v) for u,ds in graph.items() for v in ds}
gen=json.loads((ROOT/'audit.json').read_text())
assert edges=={(tuple(e['from']),tuple(e['to'])) for e in gen['edges']}
generated_id_census={(tuple(x['path'].split('.',1)[0].split('[')[0:1]),x['path'],x['id'],tuple(x['keys'])) for x in gen['integer_id_census']}
independent_id_census={(tuple(x['owner']),x['path'],x['id'],tuple(x['keys'])) for x in integer_id_rows}
# Generator paths are rooted at a kind/id prefix; compare payload-local suffix,
# id and dictionary keys to avoid relying on its traversal implementation.
def path_tail(p): return p.split('.',1)[1] if '.' in p else ''
gen_id_norm={(path_tail(x['path']),x['id'],tuple(x['keys'])) for x in gen['integer_id_census']}
ind_id_norm={(path_tail(x['path']),x['id'],tuple(x['keys'])) for x in integer_id_rows}
assert gen_id_norm==ind_id_norm, {'only_independent':sorted(ind_id_norm-gen_id_norm),'only_generator':sorted(gen_id_norm-ind_id_norm)}
report={
 'status':'PASS_INDEPENDENT_STRUCTURAL_AUDIT','input_sha256':H(SRC),'output_sha256':H(OUT),
 'pinned_charon_revision':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c',
 'pinned_charon_reorder_decls_sha256':'8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632',
 'roots':[list(n) for n in roots], 'counts':{k:sum(n[0]==k for n in visited) for k in fields},
 'ordered_count':len(ordered),'edges_count':len(edges),'edge_set_matches_generator':True,
 'typed_reference_shapes':shapes,'missing_refs':[],'cycles':[],'trait_execution_refs':[],
 'fun_trait_source_refs':[],'integer_id_dictionary_count':len(integer_id_rows),
 'integer_id_dictionary_classes':sorted({x['path'].split('.',1)[1].split('.',1)[0].split('[',1)[0] for x in integer_id_rows}),
 'integer_id_census_matches_generator':True,
 'all_dependencies_precede_users':True,'all_reachable_once_no_extra':True,
 'only_changed_json_path':'translated.ordered_decls','all_other_json_identical':True,
 'all_type_fun_global_rows_identical':True,
 'scope':'Structural metadata audit only; no translation or source-semantics claim.',
 'typed_reference_occurrences':[{'owner':list(n),'kind':k,'id':i,'path':p} for n,k,i,p in occ],
 'integer_id_dictionaries':integer_id_rows}
(HERE/'independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='typed_reference_occurrences'},indent=2))
