"""Instantiate direct calls and concrete trait dictionaries without fallbacks.
Unsupported dictionary/binder forms are explicit gaps, never discarded edges.
No theorem or complete-cone credit follows from this diagnostic alone.
"""
from pathlib import Path
import json,lzma,hashlib,sys,collections
P=Path(sys.argv[1]); x=json.load(lzma.open(P,'rt'));assert x['has_errors'] is False
t=x['translated'];tab={};errors=[]
def walk(x):
 yield x
 if isinstance(x,dict):
  for y in x.values():yield from walk(y)
 elif isinstance(x,list):
  for y in x:yield from walk(y)
for v in walk(x):
 if isinstance(v,dict)and'HashConsedValue'in v:
  n,val=v['HashConsedValue']
  if n in tab:assert tab[n]==val,('hashcons collision',n)
  tab[n]=val
fun={f['def_id']:f for f in t['fun_decls']if f};impl={r['def_id']:r for r in t['trait_impls']if r}
name=lambda f:'::'.join(c['Ident'][0]if'Ident'in c else'{impl}'for c in f['item_meta']['name'])
def unbox(v):
 while isinstance(v,dict)and('Deduplicated'in v or'HashConsedValue'in v):
  if 'Deduplicated'in v:v=tab[v['Deduplicated']]
  else:v=v['HashConsedValue'][1]
 return v
empty=dict(types=[],const_generics=[],trait_refs=[])
def sub(v,env):
 v=unbox(v)
 if isinstance(v,list):return [sub(y,env)for y in v]
 if not isinstance(v,dict):return v
 if 'TypeVar'in v and 'Free'in v['TypeVar']:
  i=v['TypeVar']['Free'];assert i<len(env['types']),('unbound type',i,env)
  return env['types'][i]
 if 'kind'in v and isinstance(v['kind'],dict):
  k=v['kind']
  if 'Clause'in k and 'Free'in k['Clause']:
   i=k['Clause']['Free'];assert i<len(env['trait_refs']),('unbound clause',i,env)
   return env['trait_refs'][i]
  if 'Var'in k and 'Free'in k['Var']:
   i=k['Var']['Free'];assert i<len(env['const_generics']),('unbound const',i,env)
   return env['const_generics'][i]
 return {k:sub(y,env)for k,y in v.items()if k!='regions'}
def resolve_ref(r):
 r=unbox(r);k=r['kind']
 if 'TraitImpl'in k:return r
 if 'ParentClause'in k:
  parent,i=k['ParentClause'];parent=resolve_ref(parent);a=parent['kind']['TraitImpl'];d=impl[a['id']]
  return resolve_ref(sub(d['implied_trait_refs'][i],a['generics']))
 raise ValueError(('unresolved dictionary',r))
def method(r,mid,callgenerics):
 r=resolve_ref(r);a=r['kind']['TraitImpl'];d=impl[a['id']];tid=r['trait_decl_ref']['skip_binder']['id']
 methods=[m for m in d['methods']if m is not None and m['kind'].get('TraitMethod')==[tid,mid]]
 assert len(methods)==1,('missing method',a['id'],tid,mid)
 m=methods[0];p=m['params']
 assert not p['types'] and not p['const_generics'],('method type/const binder unsupported',a['id'],mid,p)
 assert not callgenerics['types'] and not callgenerics['const_generics'],('method type/const arguments unsupported',callgenerics)
 assert len(p['trait_clauses'])==len(callgenerics['trait_refs']),('method clause arity',p,callgenerics)
 def bind_clauses(v):
  v=unbox(v)
  if isinstance(v,list):return [bind_clauses(z)for z in v]
  if not isinstance(v,dict):return v
  if isinstance(v.get('kind'),dict) and 'Clause'in v['kind'] and 'Bound'in v['kind']['Clause']:
   depth,index=v['kind']['Clause']['Bound'];assert depth==0,('nested method clause binder',v)
   return callgenerics['trait_refs'][index]
  # This limited binder rule is used only with no nested Binder.params.
  assert 'params'not in v,('nested method binder unsupported',v)
  return {k:bind_clauses(z)for k,z in v.items()}
 q=sub(bind_clauses(m['skip_binder']),a['generics'])
 return q['id'],q['generics']
def key(i,e):return str(i)+':'+hashlib.sha256(json.dumps(e,sort_keys=True).encode()).hexdigest()[:20]
seen={};queue=[(0,empty)];edges=[];unresolved=[];builtins=[];globals=[];aborts=[];drops=[]
while queue:
 i,e=queue.pop(0);k=key(i,e)
 if k in seen:continue
 f=fun[i];seen[k]=dict(id=i,name=name(f),environment=e,opaque=not isinstance(f['body'],dict))
 try:
  # Fail closed if an instantiated declaration retains an unresolved parameter.
  signature=sub(f['signature'],e)
 except Exception as err:
  unresolved.append(dict(caller=k,where='signature',error=repr(err)));continue
 for v in walk(f['body']):
  if not isinstance(v,dict):continue
  if 'Call'in v:
   c=v['Call']['call'];target=c['func']
   try:
    assert 'Regular'in target,('function pointer call',target)
    r=target['Regular'];kind=r['kind'];cg=sub(r['generics'],e)
    if 'Fun'in kind:
     z=kind['Fun']
     if 'Builtin'in z:builtins.append(dict(caller=k,builtin=z['Builtin'],generics=cg));continue
     j=z['Regular'];je=cg;why='direct'
    elif 'Trait'in kind:
     ref,mid=kind['Trait'];ref=sub(ref,e);j,je=method(ref,mid,cg);why='dictionary'
    else:raise ValueError(('unknown call',kind))
    assert j in fun,('missing function declaration',j)
    jk=key(j,je);edges.append(dict(caller=k,callee=jk,callee_id=j,callee_name=name(fun[j]),kind=why));queue.append((j,je))
   except Exception as err:unresolved.append(dict(caller=k,target=target,error=repr(err)))
  if 'Global'in v and isinstance(v['Global'],dict)and'id'in v['Global']:
   try:globals.append(dict(caller=k,reference=sub(v['Global'],e)))
   except Exception as err:unresolved.append(dict(caller=k,where='global',error=repr(err)))
  if 'Abort'in v:aborts.append(dict(caller=k,abort=v['Abort']))
  if 'Drop'in v:
   try:drops.append(dict(caller=k,value=sub(v['Drop'],e)))
   except Exception as err:unresolved.append(dict(caller=k,where='drop',error=repr(err)))
 assert len(seen)<5000,'review: excessive instance growth'
out=dict(input=str(P),input_sha256=hashlib.sha256(P.read_bytes()).hexdigest(),instances=seen,edges=edges,builtins=builtins,global_references=globals,aborts=aborts,drops=drops,unresolved=unresolved,complete=False,limitation='Explicit unresolved dictionaries/binders/opaque leaves remain; global initializers and source/feature association require independent checks.')
Path(sys.argv[2]).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(instances=len(seen),functions=len({r['id']for r in seen.values()}),opaque=sum(r['opaque']for r in seen.values()),dictionary_edges=sum(r['kind']=='dictionary'for r in edges),unresolved=len(unresolved),drops=len(drops))))
for r in unresolved[:12]:print(r['caller'],r.get('where','call'),r['error'][:350])
