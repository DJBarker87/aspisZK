#!/usr/bin/env python3
"""Independent saved-artifact check for R388; read-only and offline."""
import copy,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parent
SRC=R.parent/'r387-reduce-u62-extraction-preflight/R387ReduceU62.llbc'
PIN=R.parent/'r267-private-inverse-leaf-ordering/pinned-reorder_decls.rs'
INPUT='fdb448185f0f077cf0df303709da52a8be05eeb800767a4ea9a03f7f3c71afc4'
OUTPUT=R/'R388ReduceU62Ordered.llbc'
EXPECTED='95480c0a8938629f770f7c381fe61a71f44e8275fe2e7275e9edfd4a4bb7f040'
ORDER=[{'Type':{'NonRec':0}},{'Fun':{'NonRec':2}},{'Global':{'NonRec':0}},{'Fun':{'NonRec':1}},{'Fun':{'NonRec':0}}]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SRC)==INPUT and sha(PIN)=='8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632' and sha(OUTPUT)==EXPECTED
src=json.loads(SRC.read_text()); out=json.loads(OUTPUT.read_text()); st=src['translated']; ot=out['translated']
assert out['has_errors'] is False and st['ordered_decls']==[] and ot['ordered_decls']==ORDER
left=copy.deepcopy(src);right=copy.deepcopy(out);left['translated'].pop('ordered_decls');right['translated'].pop('ordered_decls');assert left==right
T={x['def_id']:x for x in st['type_decls'] if x};F={x['def_id']:x for x in st['fun_decls'] if x};G={x['def_id']:x for x in st['global_decls'] if x}
assert set(T)=={0} and set(F)=={0,1,2} and set(G)=={0}
# Decode all hash-cons values independently for typed-reference collection.
cons={}
def collect(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   k,v=x['HashConsedValue']; assert k not in cons or cons[k]==v;cons[k]=v
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(src)
def expand(x,stack=()):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   k,v=x['HashConsedValue'];assert k not in stack;return expand(v,stack+(k,))
  if 'Deduplicated' in x:
   k=x['Deduplicated'];assert k in cons and k not in stack;return expand(cons[k],stack+(k,))
  return {k:expand(v,stack) for k,v in x.items()}
 if isinstance(x,list):return [expand(v,stack) for v in x]
 return x
rows={('Type',k):v for k,v in T.items()}|{('Fun',k):v for k,v in F.items()}|{('Global',k):v for k,v in G.items()}
graph={n:set() for n in rows}; unknown=[]
def walk(x,n,path):
 if isinstance(x,dict):
  if isinstance(x.get('id'),dict) and set(x['id'])=={'Adt'} and isinstance(x['id']['Adt'],int):graph[n].add(('Type',x['id']['Adt']))
  if set(x)=={'Adt'} and isinstance(x['Adt'],int):graph[n].add(('Type',x['Adt']))
  if 'Fun' in x:
   v=x['Fun']
   if isinstance(v,dict) and set(v)=={'Regular'} and isinstance(v['Regular'],int):graph[n].add(('Fun',v['Regular']))
   elif isinstance(v,dict) and set(v)=={'Builtin'}:pass
   else:unknown.append((path+'.Fun',v))
  if 'Global' in x:
   v=x['Global']
   if isinstance(v,int):graph[n].add(('Global',v))
   elif isinstance(v,dict) and isinstance(v.get('id'),int) and 'generics' in v:graph[n].add(('Global',v['id']))
   else:unknown.append((path+'.Global',v))
  for k in ('TraitDecl','TraitImpl','TraitMethod','trait_ref','impl_ref','impl_trait'):
   if k in x:unknown.append((path+'.'+k,x[k]))
  for k,v in x.items():walk(v,n,path+'.'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x):walk(v,n,f'{path}[{i}]')
for kind,group in [('Type',T),('Fun',F),('Global',G)]:
 for i,row in group.items():
  decoded=expand(row);decoded={k:v for k,v in decoded.items() if k not in ('def_id','item_meta','src','is_global_initializer')};walk(decoded,(kind,i),f'{kind}[{i}]')
assert not unknown,unknown
assert graph=={('Type',0):set(),('Fun',0):{('Type',0),('Fun',1)},('Fun',1):{('Global',0)},('Fun',2):set(),('Global',0):{('Fun',2)}},graph
order=[('Type',0),('Fun',2),('Global',0),('Fun',1),('Fun',0)];pos={x:i for i,x in enumerate(order)}
for owner,deps in graph.items():
 for dep in deps:assert dep in rows and pos[dep]<pos[owner],(owner,dep)
# Independent cycle detection on the whole rooted graph.
color={};
def visit(n):
 if color.get(n)==1:raise AssertionError(('cycle',n))
 if color.get(n)==2:return
 color[n]=1
 for dep in graph[n]:visit(dep)
 color[n]=2
visit(('Fun',0)); assert set(color)==set(rows)
# Check source identity/path/visibility, ordered target rows unchanged.
root=F[0];m=root['item_meta'];assert m['is_local'] is False and m['span']['data']['beg']['line']==103
assert m['name'][-1]['Ident'][0]=='reduce_u62' and 'Structured' in root['body']
assert root==next(x for x in ot['fun_decls'] if x and x['def_id']==0)
print(json.dumps({'status':'PASS','ordered_ids':[[k,i] for k,i in order],'edges':{str(k):[list(x) for x in sorted(v)] for k,v in graph.items()},'missing_or_unknown_references':0,'cycles':0,'all_other_json_equal':True,'output_sha256':EXPECTED,'translation':'not run'},indent=2))
