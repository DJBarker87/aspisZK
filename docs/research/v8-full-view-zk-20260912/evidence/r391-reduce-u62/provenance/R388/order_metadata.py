#!/usr/bin/env python3
"""Metadata-only R388 topological ordering of exact R387 declarations."""
import copy, hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
INPUT=ROOT.parent/'r387-reduce-u62-extraction-preflight/R387ReduceU62.llbc'
ROOT_AUDIT=ROOT.parent/'r387-reduce-u62-extraction-preflight/body-dependency-audit.json'
PINNED=ROOT.parent/'r267-private-inverse-leaf-ordering/pinned-reorder_decls.rs'
EXPECTED_INPUT='fdb448185f0f077cf0df303709da52a8be05eeb800767a4ea9a03f7f3c71afc4'
EXPECTED_PINNED='8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(INPUT)==EXPECTED_INPUT and sha(PINNED)==EXPECTED_PINNED
assert json.loads(ROOT_AUDIT.read_text())['llbc_sha256']==EXPECTED_INPUT
raw=json.loads(INPUT.read_text()); d=raw['translated']; assert raw['has_errors'] is False and d['ordered_decls']==[]
tables={'Type':'type_decls','Fun':'fun_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}
rows={(k,x['def_id']):x for k,t in tables.items() for x in d[t] if isinstance(x,dict)}
# Collect and expand Charon hash-consed values strictly, failing on broken references/cycles.
cons={}
def collect(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in cons or cons[i]==v; cons[i]=v
  for v in x.values(): collect(v)
 elif isinstance(x,list):
  for v in x: collect(v)
collect(raw)
def decode(x,seen=()):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in seen; return decode(v,seen+(i,))
  if 'Deduplicated' in x:
   i=x['Deduplicated']; assert i in cons and i not in seen; return decode(cons[i],seen+(i,))
  return {k:decode(v,seen) for k,v in x.items()}
 if isinstance(x,list): return [decode(v,seen) for v in x]
 return x
def executable(n):
 return {k:v for k,v in decode(rows[n]).items() if k not in ('def_id','item_meta','src','is_global_initializer')}
unknown=[]; census=[]; graph={}; active=[]; done=[]; order=[]
def refs(x,node,path,out):
 if isinstance(x,dict):
  if isinstance(x.get('id'),int):
   tail=path.rsplit('.',1)[-1]; census.append({'from':[node[0],node[1]],'path':path,'id':x['id'],'keys':sorted(x)})
   if not (tail=='Global' or tail.startswith('statements[') or '.kind.Enum[' in path): unknown.append({'path':path,'ref':x})
  if isinstance(x.get('id'),dict) and set(x['id'])=={'Adt'} and isinstance(x['id']['Adt'],int): out.add(('Type',x['id']['Adt']))
  if set(x)=={'Adt'} and isinstance(x['Adt'],int): out.add(('Type',x['Adt']))
  if 'Fun' in x:
   v=x['Fun']
   if isinstance(v,dict) and set(v)=={'Regular'} and isinstance(v['Regular'],int): out.add(('Fun',v['Regular']))
   elif isinstance(v,dict) and set(v)=={'Builtin'}: pass
   else: unknown.append({'path':path+'.Fun','ref':v})
  if 'Global' in x:
   v=x['Global']
   if isinstance(v,int): out.add(('Global',v))
   elif isinstance(v,dict) and isinstance(v.get('id'),int) and 'generics' in v: out.add(('Global',v['id']))
   else: unknown.append({'path':path+'.Global','ref':v})
  for k in ('TraitDecl','TraitImpl','TraitMethod','trait_ref','impl_ref','impl_trait'):
   if k in x: unknown.append({'path':path+'.'+k,'ref':x[k]})
  for k,v in x.items(): refs(v,node,path+'.'+k,out)
 elif isinstance(x,list):
  for i,v in enumerate(x): refs(v,node,f'{path}[{i}]',out)
def visit(n):
 assert n in rows,('missing declaration',n)
 assert n[0] in ('Type','Fun','Global'),('unsupported declaration kind',n)
 if n in active: raise ValueError(('dependency cycle',active+[n]))
 if n in done:return
 active.append(n); found=set(); refs(executable(n),n,f'{n[0]}[{n[1]}]',found); graph[n]=found
 # Deterministic family precedence for this tiny graph; independently audited against all edges below.
 for dep in sorted(found,key=lambda x:({'Type':0,'Fun':1,'Global':2}[x[0]],x[1])): visit(dep)
 active.pop(); done.append(n); order.append(n)
visit(('Fun',0))
assert not unknown,unknown
expected=[('Type',0),('Fun',2),('Global',0),('Fun',1),('Fun',0)]
assert order==expected,order
pos={x:i for i,x in enumerate(order)}
assert all(pos[v]<pos[u] for u,vs in graph.items() for v in vs)
out=copy.deepcopy(raw); out['translated']['ordered_decls']=[{k:{'NonRec':i}} for k,i in order]
a=copy.deepcopy(raw); b=copy.deepcopy(out); a['translated'].pop('ordered_decls'); b['translated'].pop('ordered_decls'); assert a==b
DEST=ROOT/'R388ReduceU62Ordered.llbc'; DEST.write_text(json.dumps(out,indent=2)+'\n')
edges=[{'from':[u[0],u[1]],'to':[v[0],v[1]]} for u,vs in graph.items() for v in sorted(vs)]
row_hashes=[]
for kind,table in tables.items():
 for row in d[table]:
  if isinstance(row,dict): row_hashes.append({'kind':kind,'id':row['def_id'],'input_row_sha256':hashlib.sha256(json.dumps(row,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
report={'input_sha256':EXPECTED_INPUT,'output_sha256':sha(DEST),'pinned_reorder_source_sha256':EXPECTED_PINNED,'root_audit_sha256':sha(ROOT_AUDIT),'root_ids':[['Fun',0]],'ordered_ids':[[k,i] for k,i in order],'counts':{k:sum(x[0]==k for x in order) for k in ('Type','Fun','Global')},'complete_input_table_counts':{k:len(d[v]) for k,v in tables.items()},'only_changed_json_path':'translated.ordered_decls','all_other_input_json_equal':True,'topological_dependencies_precede_consumers':True,'edges':edges,'integer_id_reference_census':census,'unknown_references':unknown,'missing_references':[],'cycles':[],'row_hashes':row_hashes,'scope':'Only ordered_decls metadata changes. All original rows and source/body/signature/type/options remain unchanged; no translation or theorem is established.'}
(ROOT/'generator-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'ordered_ids':report['ordered_ids'],'edges':edges,'output_sha256':report['output_sha256'],'unknown_refs':len(unknown)},indent=2))
