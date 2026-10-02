"""Repair only declaration-order metadata of the exact R281 two QM31 field roots.
Fails closed on missing/unclassified refs, traits, cycles, or changed source rows.
This is a metadata generator, never a replacement for source execution proof.
"""
import json,hashlib,pathlib,copy
ROOT=pathlib.Path(__file__).resolve().parent
SRC=ROOT.parent/'r281-private-field-leaves-extract/R281PrivateFieldLeaves.llbc'
ROOT_AUDIT=ROOT.parent/'r281-private-field-leaves-extract/root-body-inspection.json'
PINNED=ROOT.parent/'r267-private-inverse-leaf-ordering/pinned-reorder_decls.rs'
EXPECTED='6ffca95bc433f10b0b01db769cdb76c9f99421c0d7c3cfb7b4644af2e33b3f01'
EXPECTED_ROOT_AUDIT='41d46d9da7ebc64e44d3100f57b788fbb80b0f0260122ccbc5f0d4395d3c5c9b'
EXPECTED_PINNED='8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SRC)==EXPECTED
assert sha(ROOT_AUDIT)==EXPECTED_ROOT_AUDIT and sha(PINNED)==EXPECTED_PINNED
raw=json.loads(SRC.read_text()); d=raw['translated']; assert d['ordered_decls']==[] and raw['has_errors'] is False
tab={}
def collect(x):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:
   i,v=x['HashConsedValue'];assert i not in tab or tab[i]==v;tab[i]=v
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(raw)
def decode(x,seen=()):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:
   i,v=x['HashConsedValue'];assert i not in seen;return decode(v,seen+(i,))
  if 'Deduplicated'in x:
   i=x['Deduplicated'];assert i in tab and i not in seen;return decode(tab[i],seen+(i,))
  return{k:decode(v,seen)for k,v in x.items()}
 if isinstance(x,list):return[decode(v,seen)for v in x]
 return x
GROUPS={'Type':'type_decls','Fun':'fun_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}
ORDER_GROUPS={k:GROUPS[k] for k in ('Type','Fun','Global')}
rows={ (k,x['def_id']):x for k,t in GROUPS.items()for x in d[t]if isinstance(x,dict)}
ROOTS=[('Fun',0),('Fun',1)]
root_audit=json.loads(ROOT_AUDIT.read_text()); assert root_audit['has_errors'] is False
for k,i in ROOTS:
 row=rows[(k,i)]; assert isinstance(row['body'],dict) and 'Structured' in row['body']
 # These roots live in frozen aspis_core dependency field.rs; Charon's is_local
 # flag is false. The pinned artifact audit binds exact method names/spans/source hash.
 assert row['item_meta']['is_local'] is False
assert [root_audit['selected_roots'][n]['fun_id'] for n in ('neg','mul_m31')]==[0,1]
# ItemMeta and ItemSource are skipped by pinned Charon DepsForItem. This generator
# intentionally orders only Type/Fun/Global and fails closed if the R281 closure
# includes any trait dependency.
def executable_row(n):
 x=decode(rows[n]);return{k:v for k,v in x.items()if k not in ('def_id','item_meta','src','is_global_initializer')}
edges=[];id_census=[]
def references(x,path,found):
 if isinstance(x,dict):
  if isinstance(x.get('id'),int):
   end=path.rsplit('.',1)[-1];id_census.append({'path':path,'id':x['id'],'keys':sorted(x)})
   assert end=='Global' or end.startswith('statements[') or '.kind.Enum['in path,(path,x)
  adt=x.get('id')
  if isinstance(adt,dict) and set(adt)=={'Adt'} and isinstance(adt['Adt'],int):found.add(('Type',adt['Adt']))
  if set(x)=={'Adt'} and isinstance(x['Adt'],int):found.add(('Type',x['Adt']))
  if isinstance(x.get('Fun'),dict):
   f=x['Fun']
   if set(f)=={'Regular'}:assert isinstance(f['Regular'],int);found.add(('Fun',f['Regular']))
   elif set(f)=={'Builtin'}:pass
   else:raise ValueError(('unclassified function ref',path,f))
  if 'Global'in x:
   g=x['Global']
   if isinstance(g,int):found.add(('Global',g))
   elif isinstance(g,dict) and isinstance(g.get('id'),int) and 'generics'in g:found.add(('Global',g['id']))
   else:raise ValueError(('unclassified Global ref',path,g))
  for key in ('TraitDecl','TraitImpl','TraitMethod','trait_ref','impl_ref','impl_trait'):
   assert key not in x,('trait frontier not supported in this small generator',path,key)
  for k,v in x.items():references(v,path+'.'+k,found)
 elif isinstance(x,list):
  for i,v in enumerate(x):references(v,path+f'[{i}]',found)
graph={};active=set();ordered=[];visited=set()
def visit(n):
 assert n in rows,('missing declaration',n)
 assert n[0]in ('Type','Fun','Global'),n
 assert n not in active,('cycle requires explicit SCC handling',n)
 if n in visited:return
 active.add(n);refs=set();references(executable_row(n),f'{n[0]}[{n[1]}]',refs);graph[n]=refs
 for dep in sorted(refs):
  edges.append({'from':list(n),'to':list(dep)});visit(dep)
 active.remove(n);visited.add(n);ordered.append(n)
for n in ROOTS:visit(n)
position={n:i for i,n in enumerate(ordered)}
assert all(position[v]<position[u]for u,refs in graph.items()for v in refs)
# No emitted item is altered, removed, made opaque, or replaced. Existing
# options, source files and hash-consed values remain exactly equal.
out=copy.deepcopy(raw);out['translated']['ordered_decls']=[{k:{'NonRec':i}}for k,i in ordered]
before=copy.deepcopy(raw);after=copy.deepcopy(out);before['translated'].pop('ordered_decls');after['translated'].pop('ordered_decls');assert before==after
DEST=ROOT/'R284PrivateFieldLeavesOrdered.llbc';DEST.write_text(json.dumps(out,indent=2)+'\n')
checks=[]
for n,row in rows.items():
 other=next(x for x in out['translated'][GROUPS[n[0]]]if isinstance(x,dict)and x['def_id']==n[1]);assert row==other
 checks.append({'kind':n[0],'id':n[1],'serialized_value_identical':True,'decoded_sha256':hashlib.sha256(json.dumps(decode(row),sort_keys=True,separators=(',',':')).encode()).hexdigest()})
report={'input_sha256':EXPECTED,'root_body_inspection_sha256':EXPECTED_ROOT_AUDIT,'pinned_reorder_source_sha256':EXPECTED_PINNED,'output_sha256':sha(DEST),'root_ids':[list(n)for n in ROOTS],'ordered_ids':[list(n)for n in ordered],'counts':{k:sum(n[0]==k for n in ordered)for k in ORDER_GROUPS},'complete_input_table_counts':{k:len(d[t])for k,t in GROUPS.items()},'only_changed_json_path':'translated.ordered_decls','all_original_declaration_rows_identical':True,'all_dependency_edges_before_use':True,'missing_references':[],'cycles':[],'traits_in_execution_closure':False,'root_metadata_is_local':False,'root_bodies_structured':True,'row_checks':checks,'edges':edges,'integer_id_census':id_census,'scope':'Metadata-only order repair. No translation, source execution, standard-library semantics, theorem or release gate is established by this generator.'}
(ROOT/'audit.json').write_text(json.dumps(report,indent=2)+'\n');print(report['counts']);print(report['output_sha256'])
