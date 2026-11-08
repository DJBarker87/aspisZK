from pathlib import Path
import json,lzma
p=json.loads(lzma.decompress(Path('evidence/pv-lib-20261107/lane-A/session5/thread-llbc.json.xz').read_bytes()))['translated'];d={}
def walk(x):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:i,v=x['HashConsedValue'];d[i]=v
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(p)
def normal(x):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:return normal(x['HashConsedValue'][1])
  if 'Deduplicated'in x:return normal(d[x['Deduplicated']])
  return {k:normal(v) for k,v in x.items()}
 if isinstance(x,list):return list(map(normal,x))
 return x
if __name__=='__main__':
 for i in [124,222,360,405,486,584]:
  f=normal(p['fun_decls'][i]);print('FN',i)
  def inspect(x):
   if isinstance(x,dict):
    if 'kind'in x and 'id'in x and isinstance(x['kind'],dict):
     k=x['kind']
     if 'Call'in k:print(x['id'],'CALL',k['Call']['call']['func'])
     elif 'Drop'in k:print(x['id'],'DROP',k['Drop']['fn_ptr'])
    for v in x.values():inspect(v)
   elif isinstance(x,list):
    for v in x:inspect(v)
  inspect(f['body'])
