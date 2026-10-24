"""Reach operations through actual Error/NonZero/Inner projections."""
from pathlib import Path
D=Path(__file__).resolve().parent
# Reuse only fixture encoding helpers, no extraction invocation.
exec((D/'negative005.py').read_text().split('# Direct leaf operations')[0])
error=copy.deepcopy(t['fun_decls'][3]['signature']['inputs'][0])
nonzero=copy.deepcopy(t['type_decls'][0]['kind']['Struct'][0]['ty'])
inner=copy.deepcopy(nonzero['ExpandedTy']['Adt']['generics']['types'][1])
proj=lambda p,tid,ty:dict(kind={'Projection':[p,{'Field':[{'Adt':[tid,None]},0]}]},ty=ty)
leaf=proj(proj(proj(place(1,error),0,nonzero),4,inner),6,pattern)
function('project_compare',error,boolean,[assign(place(0,boolean),{'BinaryOp':['Eq',{'Copy':leaf},{'Copy':leaf}]})])
for name,op,out in [('cast',{'Cast':{'Scalar':[{'Int':'I32'},{'Int':'I32'}]}},i32),('mutate','Not',pattern),('transmute',{'Cast':{'Transmute':[pattern,i32]}},i32)]:
 if name=='mutate':
  kinds=[assign(leaf,{'UnaryOp':[op,{'Copy':leaf}]}),assign(place(0,error),use(1,error))];out=error
 else:kinds=[assign(place(0,out),{'UnaryOp':[op,{'Copy':leaf}]})]
 function('project_'+name,error,out,kinds)
function('outer_uninitialized',error,error,[assign(place(0,error),use(2,error))])
function('outer_moved',error,error,[assign(place(2,error),use(1,error)),assign(place(0,error),use(1,error))])
for n in ['0','1']:
 c=dict(kind={'Literal':{'Scalar':{'Signed':['I32',n]}}},ty=pattern)
 function('project_construct_'+n,error,error,[assign(leaf,{'Use':[{'Const':c},'Yes']}),assign(place(0,error),use(1,error))])
# Fresh hashcons serialization follows the fixed fixture recipe.
tail=(D/'negative005.py').read_text().split('# Serialize a fresh, consistent hashcons table after mutation.')[1]
tail=tail.replace('negative007','projected008').replace("len(t['fun_decls'])-9", "len(t['fun_decls'])-8")
exec(tail)
