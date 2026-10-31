"""Direct runtime edge inventory of the original (unrewritten) extraction.
Never treats a signature/trait/vtable reference as a runtime call. Opaque leaves,
unresolved dispatch, and global initializer dependencies are explicit gaps.
"""
from pathlib import Path
import lzma,json,hashlib,collections
P=Path('evidence/pv-b3p6-20261028/llbc-resume5/PV_B3P_227_resume5.llbc.xz')
raw=lzma.decompress(P.read_bytes());x=json.loads(raw);t=x['translated'];assert not x['has_errors']
funs={f['def_id']:f for f in t['fun_decls'] if f is not None}
def name(f):
 return '::'.join(c['Ident'][0] if 'Ident'in c else '{impl}' for c in f['item_meta']['name'])
def walk(x,path=()):
 yield path,x
 if isinstance(x,dict):
  for k,v in x.items():yield from walk(v,path+(k,))
 elif isinstance(x,list):
  for i,v in enumerate(x):yield from walk(v,path+(i,))
seen=set();todo=[0];edges=[];unresolved=[];builtins=[];globals=[];aborts=[];drops=[]
while todo:
 i=todo.pop()
 if i in seen:continue
 assert i in funs,('missing direct function',i)
 seen.add(i);f=funs[i]
 for path,v in walk(f['body']):
  if not isinstance(v,dict):continue
  if 'Call'in v:
   c=v['Call']['call']; callee=c['func']; r=callee.get('Regular',{}).get('kind',{}).get('Fun',{})
   if 'Regular'in r:
    j=r['Regular'];edges.append(dict(caller=i,callee=j,caller_name=name(f),callee_name=name(funs[j]),call=c,path=path));todo.append(j)
   elif 'Builtin'in r:builtins.append(dict(caller=i,caller_name=name(f),builtin=r['Builtin'],call=c,path=path))
   else:unresolved.append(dict(caller=i,caller_name=name(f),func=callee,call=c,path=path))
  if 'Abort'in v:aborts.append(dict(caller=i,caller_name=name(f),abort=v['Abort'],path=path))
  if 'Global'in v and isinstance(v['Global'],dict) and 'id'in v['Global']:globals.append(dict(caller=i,global_id=v['Global']['id'],path=path))
  if 'Drop'in v:drops.append(dict(caller=i,value=v['Drop'],path=path))
rows=[dict(id=i,name=name(funs[i]),opaque=not isinstance(funs[i]['body'],dict),source=funs[i]['item_meta'].get('source_text'),span=funs[i]['item_meta']['span'],signature=funs[i]['signature'])for i in sorted(seen)]
x=dict(input=str(P),llbc_sha256=hashlib.sha256(raw).hexdigest(),compressed_sha256=hashlib.sha256(P.read_bytes()).hexdigest(),root=0,root_name=name(funs[0]),options=t['options'],functions=rows,edges=edges,builtins=builtins,unresolved_calls=unresolved,global_references=globals,aborts=aborts,drops=drops,complete=False,reason='Opaque callees and global initializers must be resolved before completeness; original extraction source authority/configuration and source-to-deployed association are separate checks.')
Path('evidence/pv-b3q2-20261031/original-callcone.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(functions=len(rows),edges=len(edges),opaque=sum(r['opaque']for r in rows),unresolved=len(unresolved),builtins=len(builtins),globals=len(globals),aborts=len(aborts),drops=len(drops))))
for r in rows:
 if r['opaque']:print('OPAQUE',r['id'],r['name'])
for r in unresolved:print('UNRESOLVED',r['caller_name'],r['func'])
