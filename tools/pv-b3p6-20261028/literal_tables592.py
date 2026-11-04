"""Read complete LLBC initializers consisting solely of unsigned literals,
aggregate construction, local moves/copies, storage markers and return.
No calls, external reads, branches, mutation through pointers or missing
statements are accepted. This is a scalar projection, not native initialization.
"""
import copy
from initializer_source578 import compact
from kind_panic587 import unsigned

def initialize(f):
 b=f['body']['Structured'];assert b['locals']['arg_count']==0
 env={};events=[];returned=False
 def operand(o):
  if 'Const'in o:return unsigned(o['Const'])
  tag,p=next(iter(o.items()));assert tag in['Copy','Move']and'Local'in p['kind']
  slot=p['kind']['Local'];v=copy.deepcopy(env[slot])
  if tag=='Move':del env[slot]
  return v
 for st in b['body']['statements']:
  assert not returned
  k=st['kind']
  if k=='Return':returned=True;continue
  assert isinstance(k,dict)
  if'StorageLive'in k or'StorageDead'in k:continue
  if 'Call'in k:
   assert list(k)==['Call'];call=k['Call']['call'];fun=call['func']['Regular'];assert fun['kind']['Fun']=={'Builtin':'ArrayRepeat'}
   cs=fun['generics']['const_generics'];assert len(cs)==1 and len(call['args'])==1
   n=unsigned(cs[0]);value=operand(call['args'][0]);dest=call['dest'];assert list(dest['kind'])==['Local']
   assert all(q['kind']=={'Abort':'UndefinedBehavior'}for q in k['Call']['on_unwind']['statements'])
   env[dest['kind']['Local']]=dict(tag={'Array':[None,compact(cs[0])]},fields=[copy.deepcopy(value)for _ in range(n)])
   events.append(st['id']);continue
  assert list(k)==['Assign'];dest,rhs=k['Assign'];assert list(dest['kind'])==['Local']
  if'Use'in rhs:assert list(rhs)==['Use'];v=operand(rhs['Use'][0])
  else:
   assert list(rhs)==['Aggregate'];tag,fields=rhs['Aggregate'];v=dict(tag=compact(tag),fields=[operand(o)for o in fields])
  env[dest['kind']['Local']]=v;events.append(st['id'])
 assert returned and set(env)=={0}
 def validate(v):
  if isinstance(v,int):return
  if'Array'in v['tag']:
   assert unsigned(v['tag']['Array'][1])==len(v['fields'])
  else:assert'Adt'in v['tag']
  for field in v['fields']:validate(field)
 validate(env[0]);return env[0],events
