"""Exact source-location and unique-assignment expression inventory of index calls.
No completeness claim: unknown expressions retain their actual AST and source.
"""
from pathlib import Path
import json,lzma,collections,hashlib
P=Path('evidence/pv-b3q2-20261031/PV_B3Q_ApplicationCone.llbc.xz')
x=json.load(lzma.open(P,'rt'));t=x['translated'];g=json.load(open('evidence/pv-b3q2-20261031/app-callcone.json'));funs={f['def_id']:f for f in t['fun_decls']if f}
def walk(x,path=()):
 yield path,x
 if isinstance(x,dict):
  for k,v in x.items():yield from walk(v,path+(k,))
 elif isinstance(x,list):
  for i,v in enumerate(x):yield from walk(v,path+(i,))
def locate(x,path):
 for k in path:x=x[k]
 return x
def literal(x):
 try:return int(x['kind']['Literal']['Scalar']['Unsigned'][1])
 except (KeyError,TypeError):return None
out=[]
for fid in sorted({r['caller']for r in g['builtins']if isinstance(r['builtin'],dict)and'Index'in r['builtin']}):
 f=funs[fid];body=f['body'];assign=collections.defaultdict(list);local=body['Structured']['locals']['locals'];names={r['index']:r.get('name')for r in local}
 for path,v in walk(body):
  if isinstance(v,dict)and'Assign'in v:
   place,rval=v['Assign']
   if 'Local'in place['kind']:assign[place['kind']['Local']].append(rval)
 def place(p,seen=()):
  k=p['kind']
  if 'Local'in k:
   i=k['Local'];vs=assign[i]
   if len(vs)==1 and i not in seen:return rval(vs[0],seen+(i,))
   return names.get(i) or f'local{i}'
  if 'Projection'in k:
   base,proj=k['Projection'];b=place(base,seen)
   if proj=='Deref':return b
   return dict(projection=b,selector=proj)
  if 'Global'in k:return dict(global_id=k['Global']['id'])
  return dict(unknown_place=k)
 def operand(o,seen=()):
  for k in ['Copy','Move']:
   if k in o:return place(o[k],seen)
  if 'Const'in o:
   v=literal(o['Const']);return v if v is not None else dict(constant=o['Const'])
  return dict(unknown_operand=o)
 def rval(v,seen=()):
  if 'Use'in v:return operand(v['Use'][0],seen)
  if 'BinaryOp'in v:
   op,a,b=v['BinaryOp'];a=operand(a,seen);b=operand(b,seen)
   return dict(op=op,args=[a,b])
  if 'UnaryOp'in v:
   op,a=v['UnaryOp'];return dict(op=op,args=[operand(a,seen)])
  if 'Ref'in v:return place(v['Ref']['place'],seen)
  return dict(unknown_rvalue=v)
 rows=[]
 for r in [r for r in g['builtins']if r['caller']==fid and isinstance(r['builtin'],dict)and'Index'in r['builtin']]:
  path=tuple(r['path']);span=None
  for j in range(len(path),-1,-1):
   v=locate(body,path[:j])
   if isinstance(v,dict)and'span'in v:span=v['span'];break
  expr=operand(r['call']['args'][-1]);ns=r['call']['func']['Regular']['generics']['const_generics'];n=literal(ns[0])if ns else None
  rows.append(dict(path=path,span=span,index=expr,array_length=n,source_ast=r['call']['args'][-1],constant_checked=isinstance(expr,int)and n is not None and expr<n))
 out.append(dict(id=fid,name=next(r['name']for r in g['functions']if r['id']==fid),source=f['item_meta']['source_text'],span=f['item_meta']['span'],rows=rows))
D=Path('evidence/pv-b3q2-20261031');(D/'index-obligations.json').write_text(json.dumps(dict(input=str(P),sha256=hashlib.sha256(P.read_bytes()).hexdigest(),functions=out,complete=False),indent=2)+'\n')
for r in out:
 print(r['id'],r['name'],len(r['rows']),'constant',sum(x['constant_checked']for x in r['rows']))
 for x in r['rows']:
  if not x['constant_checked']:print(' ',str(x['index'])[:200],'<',x['array_length'])
