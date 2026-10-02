"""Independent mechanical audit of R284 metadata ordering against frozen R281."""
import copy, hashlib, json, pathlib
HERE = pathlib.Path(__file__).resolve().parent
BASE = HERE.parent
SRC = BASE.parent / 'r281-private-field-leaves-extract/R281PrivateFieldLeaves.llbc'
ROOT_AUDIT = BASE.parent / 'r281-private-field-leaves-extract/root-body-inspection.json'
ORDERED = BASE / 'R284PrivateFieldLeavesOrdered.llbc'
PINNED = BASE.parent / 'r267-private-inverse-leaf-ordering/pinned-reorder_decls.rs'
EXPECTED = {
 'input': '6ffca95bc433f10b0b01db769cdb76c9f99421c0d7c3cfb7b4644af2e33b3f01',
 'root_inspection': '41d46d9da7ebc64e44d3100f57b788fbb80b0f0260122ccbc5f0d4395d3c5c9b',
 'pinned_rules': '8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632',
 'ordered': '37a693d55297515db02c3284f87226b8fc5f0df31cceeb3ec0d16460a69ddce5',
}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for label, path in [('input',SRC),('root_inspection',ROOT_AUDIT),('pinned_rules',PINNED),('ordered',ORDERED)]:
 assert sha(path) == EXPECTED[label], (label, sha(path))
raw, out = json.loads(SRC.read_text()), json.loads(ORDERED.read_text())
assert raw['has_errors'] is False and raw['translated']['ordered_decls'] == []
assert out['has_errors'] is False
before, after = copy.deepcopy(raw), copy.deepcopy(out)
before['translated'].pop('ordered_decls'); after['translated'].pop('ordered_decls')
assert before == after, 'non-order metadata changed'
D, O = raw['translated'], out['translated']
tables = {'Type':'type_decls','Fun':'fun_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}
counts = {kind:len(D[field]) for kind,field in tables.items()}
assert counts == {'Type':3,'Fun':8,'Global':1,'TraitDecl':0,'TraitImpl':0}, counts
rows={(kind,row['def_id']):row for kind,field in tables.items() for row in D[field]}
for key in rows:
 other=next(r for r in O[tables[key[0]]] if r['def_id']==key[1])
 assert rows[key] == other

# Decode only Charon's hash-consing wrappers, then collect typed references.
cons={}
def collect_cons(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in cons or cons[i]==v; cons[i]=v
  for v in x.values(): collect_cons(v)
 elif isinstance(x,list):
  for v in x: collect_cons(v)
collect_cons(raw)
def decode(x, seen=()):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in seen; return decode(v,seen+(i,))
  if 'Deduplicated' in x:
   i=x['Deduplicated']; assert i in cons and i not in seen; return decode(cons[i],seen+(i,))
  return {k:decode(v,seen) for k,v in x.items()}
 if isinstance(x,list): return [decode(v,seen) for v in x]
 return x

def refs(x, found):
 if isinstance(x,dict):
  if set(x)=={'Adt'} and isinstance(x['Adt'],int): found.add(('Type',x['Adt']))
  if isinstance(x.get('id'),dict) and set(x['id'])=={'Adt'} and isinstance(x['id']['Adt'],int): found.add(('Type',x['id']['Adt']))
  if isinstance(x.get('Fun'),dict):
   f=x['Fun']
   if set(f)=={'Regular'}: found.add(('Fun',f['Regular']))
   elif set(f)!={'Builtin'}: raise AssertionError(('unclassified Fun ref',f))
  if 'Global' in x:
   g=x['Global']
   if isinstance(g,int): found.add(('Global',g))
   elif isinstance(g,dict) and isinstance(g.get('id'),int) and 'generics' in g: found.add(('Global',g['id']))
   else: raise AssertionError(('unclassified Global ref',g))
  for forbidden in ('TraitDecl','TraitImpl','TraitMethod','trait_ref','impl_ref','impl_trait'):
   assert forbidden not in x, ('unexpected trait ref',forbidden)
  for v in x.values(): refs(v,found)
 elif isinstance(x,list):
  for v in x: refs(v,found)

def executable(n):
 x=decode(rows[n]); return {k:v for k,v in x.items() if k not in ('def_id','item_meta','src','is_global_initializer')}
graph={}; active=set(); visited=set(); ordered=[]
def visit(n):
 assert n in rows and n[0] in ('Type','Fun','Global'), ('missing/out-of-scope',n)
 assert n not in active, ('cycle',n)
 if n in visited:return
 active.add(n); found=set(); refs(executable(n),found); graph[n]=found
 for d in sorted(found): visit(d)
 active.remove(n); visited.add(n); ordered.append(n)
roots=[('Fun',0),('Fun',1)]
for root in roots: visit(root)
position={n:i for i,n in enumerate(ordered)}
assert len(ordered)==12 and set(ordered)==set(rows)
assert all(position[d]<position[n] for n,ds in graph.items() for d in ds)
def declaration_ids(ds):
 ans=[]
 for d in ds:
  assert len(d)==1
  kind, group=next(iter(d.items())); assert len(group)==1 and 'NonRec' in group, d
  ans.append((kind,group['NonRec']))
 return ans
emitted=declaration_ids(O['ordered_decls'])
assert emitted==ordered
assert len(emitted)==12 and len(set(emitted))==12
edges=[{'from':list(n),'to':list(d)} for n,ds in graph.items() for d in sorted(ds)]

# Verify external root metadata and its frozen source-span audit. The source bytes
# are represented by the recorded frozen hash; this script makes no semantic claim.
ra=json.loads(ROOT_AUDIT.read_text())
assert ra['has_errors'] is False and ra['translation_run'] is False
assert ra['frozen_source_hash']=='639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499'
expected_roots={'neg':(0,874),'mul_m31':(1,927)}
root_metadata={}
for name,(fid,line) in expected_roots.items():
 row=rows[('Fun',fid)]; meta=row['item_meta']; span=meta['span']['data']
 assert meta['is_local'] is False and span['file_id']==0 and span['beg']['line']==line and span['end']['line']==line
 assert isinstance(row['body'],dict) and 'Structured' in row['body']
 record=ra['selected_roots'][name]
 assert record['fun_id']==fid and record['source_line']==line and record['body_kind']=='Structured'
 assert record['item_meta_is_local'] is False
 root_metadata[name]={'fun_id':fid,'external_item_meta_is_local':False,'body_kind':'Structured','file_id':0,'line':line,'recorded_frozen_source_sha256':ra['frozen_source_hash'],'method_label':name}

# Pinned source audit: ensure relevant behavior is present in exact pinned bytes.
pinned=PINNED.read_text()
needles=['fn insert_node(', 'fn insert_edge(', 'fn enter_type_decl_id(', 'fn enter_global_decl_id(', 'fn enter_fun_decl_id(', 'fn visit_item_meta(', 'fn visit_item_source(', 'Skip `d.is_global_initializer`', "Therefore we don't explore the default const/method ids."]
assert all(s in pinned for s in needles)
report={
 'audit_kind':'independent metadata-only consistency audit',
 'hashes':{k:sha(p) for k,p in [('input',SRC),('root_inspection',ROOT_AUDIT),('pinned_rules',PINNED),('ordered',ORDERED)]},
 'input_declaration_counts':counts,
 'changed_json_paths':['translated.ordered_decls'],
 'non_order_json_identical':True,
 'reachable_declaration_counts':{'Type':sum(k=='Type' for k,_ in ordered),'Fun':sum(k=='Fun' for k,_ in ordered),'Global':sum(k=='Global' for k,_ in ordered)},
 'reachable_ids':[list(n) for n in ordered],
 'ordered_ids':[list(n) for n in emitted],
 'typed_dependency_edges':edges,
 'all_dependencies_precede_use':True,
 'missing_references':[],
 'cycles':[],
 'traits_in_tables_or_reachable_graph':False,
 'trait_defaults_applicable':'none: source LLBC trait declaration and implementation tables are empty',
 'pinned_reorder_rules_checked':{
   'only_translated_items_added_to_dependency_graph':True,
   'typed_fun_type_global_edges':True,
   'ItemMeta_and_ItemSource_skipped':True,
   'function_global_initializer_not_visited':True,
   'trait_default_callable_ids_not_dependency_edges':True,
   'trait_default_items_become_nodes_if_present':True,
 },
 'root_metadata':root_metadata,
 'boundary':'Mechanical metadata audit only. This does not accept external roots, establish source semantics/correspondence, translate LLBC, or close a theorem/release gate.'
}
(HERE/'independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'counts':report['reachable_declaration_counts'],'edges':len(edges),'root_metadata':root_metadata},indent=2))
