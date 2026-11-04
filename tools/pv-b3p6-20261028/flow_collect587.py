"""Nested-loop frame-preserving scalar dominance. Retain only facts common to EVERY
continuing branch; a terminating branch contributes no state to the join.
No bounds are inferred from a name, callback, or unreachable code.
"""
from pathlib import Path
import argparse,copy,hashlib,json,lzma
from fixed_indices572 import literal
from frame_indices578 import root,dicts
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def collect(body,range_seeds=None,windows=False):
 frames=[]
 range_seeds=range_seeds or {}
 exposed={root(x[tag]['place'])for x in dicts(body)for tag in ('Ref','RawPtr')if tag in x and isinstance(x[tag],dict)and 'place'in x[tag]}
 rows=[]
 def block(b,values,bounds,scope):
  values=dict(values);bounds=dict(bounds)
  def op(o,sid):
   if 'Const'in o:
    n=literal(o['Const']);return ('literal',n)if n is not None else None
   for tag in ('Copy','Move'):
    if tag in o and 'Projection'in o[tag]['kind']:
     base,projection=o[tag]['kind']['Projection'];mark=values.get(base.get('kind',{}).get('Local'))
     if projection=={'Field':[{'Adt':[16,1]},0]} and mark is not None and mark[0]=='rangeOption':
      value=('rangeItem',mark[1]);bounds[value]=(mark[2],mark[1],mark[3]);return value
    if tag in o and 'Local'in o[tag]['kind']:
     slot=o[tag]['kind']['Local']
     if slot not in values:values[slot]=('snapshot',scope,sid,slot)
     return values[slot]
   return None
  def moves(x):
   for n in dicts(x):
    if 'Move'in n:values.pop(root(n['Move']),None)
  def effect():
   for slot in exposed:values.pop(slot,None)
  for st in b['statements']:
   sid=st['id'];k=st['kind']
   if not isinstance(k,dict):
    if k in ['Return','UnwindResume']:return {},{},False
    values.clear();bounds.clear();continue
   if 'Assign'in k:
    dest,rhs=k['Assign'];slot=root(dest);v=op(rhs['Use'][0],sid)if 'Use'in rhs else None
    if 'BinaryOp'in rhs:
     operator,left,right=rhs['BinaryOp'];a,c=op(left,sid),op(right,sid)
     if operator in ['Lt','Ge'] and a is not None and c is not None and c[0]=='literal':v=('less'if operator=='Lt'else'notLess',a,c[1],sid)
     if windows and a is not None and c is not None:
      if operator=={'Add':'Wrap'}:v=('wrapadd',a,c)
      elif operator=={'Sub':'Wrap'}:v=('wrapsub',a,c)
      elif operator=='Ge':v=('ge',a,c,sid)
      elif operator=='Le':v=('ge',c,a,sid)
      elif operator=='Lt'and c[0]=='wrapadd'and c[2][0]=='literal':v=('windowLess',a,c[1],c[2][1],sid)
    moves(rhs);values.pop(slot,None)
    if 'Local'in dest['kind']:values[slot]=v if v is not None else('snapshot',scope,sid,slot)
    else:effect()
   elif 'StorageDead'in k or 'StorageLive'in k:values.pop(next(iter(k.values())),None)
   elif 'Call'in k:
    call=k['Call']['call'];fun=call['func'].get('Regular',{});builtin=fun.get('kind',{}).get('Fun',{}).get('Builtin',{});idx=builtin.get('Index',{})if isinstance(builtin,dict)else{}
    if idx.get('is_array')is True and idx.get('is_range')is False:
     index=op(call['args'][-1],sid);cs=fun.get('generics',{}).get('const_generics',[]);length=literal(cs[0])if len(cs)==1 else None
     if index in bounds and length is not None:
      limit,predicate,branch=bounds[index]
      if limit<=length:rows.append(dict(statement=sid,index_snapshot=index,limit=limit,length=length,slack=length-limit,predicate_statement=predicate,dominating_branch=branch,source_call=st))
    if windows and idx.get('is_array')is True and idx.get('is_range')is False and length is not None and index is not None and index[0]=='wrapsub':
     value,base=index[1:];lower=bounds.get(('lower',value,base))
     if lower is not None:
      for key,upper in bounds.items():
       if key[:3]==('upper',value,base)and key[3]<=length:
        width=key[3];rows.append(dict(statement=sid,kind='window',value_snapshot=value,base_snapshot=base,limit=width,length=length,slack=length-width,lower_test=lower,upper_test=upper,source_call=st));break
    moves(call['args']);values.pop(root(call.get('dest',{})),None);effect()
    if k['Call'].get('on_unwind'):block(k['Call']['on_unwind'],values,bounds,scope)
   elif 'Drop'in k:
    values.pop(root(k['Drop']['place']),None);effect()
    if k['Drop'].get('on_unwind'):block(k['Drop']['on_unwind'],values,bounds,scope)
   elif 'Assert'in k:moves(k['Assert'])
   elif 'Switch'in k:
    tag,v=next(iter(k['Switch'].items()));cond=op(v[0],sid)if tag=='If'else None;moves(v[0])
    if tag=='If':branches=v[1:]
    elif tag=='Match':branches=[b for _,b in v[1]]+([v[2]]if v[2]else[])
    elif tag=='SwitchInt':branches=[b for _,b in v[2]]+([v[3]]if v[3]else[])
    else:raise AssertionError(tag)
    exits=[]
    for i,child in enumerate(branches):
     child_bounds=dict(bounds)
     if tag=='If'and cond is not None and ((i==0 and cond[0]=='less')or(i==1 and cond[0]=='notLess')):child_bounds[cond[1]]=(cond[2],cond[3],sid)
     if windows and tag=='If'and i==0 and cond is not None:
      if cond[0]=='ge':child_bounds[('lower',cond[1],cond[2])]=(cond[3],sid)
      elif cond[0]=='windowLess':child_bounds[('upper',cond[1],cond[2],cond[3])]=(cond[4],sid)
     out=block(child,values,child_bounds,scope)
     if out[2]:exits.append(out)
    values={slot:value for slot,value in exits[0][0].items()if all(e[0].get(slot)==value for e in exits[1:])}if exits else{}
    # Intersect facts over all and only continuing paths.
    if not exits:return {},{},False
    bounds={key:value for key,value in exits[0][1].items()if all(e[1].get(key)==value for e in exits[1:])}
    if sid in range_seeds:
     slot,limit,next_statement=range_seeds[sid]
     values[slot]=('rangeOption',next_statement,limit,sid)
   elif 'Loop'in k:
    # Keep only locals whose stack slots have no escaping address anywhere
    # and no assignment/lifetime/move/drop in the entire nested loop.
    killed=set(exposed)
    for x in dicts(k['Loop']):
     kk=x.get('kind')
     if isinstance(kk,dict):
      if 'Assign'in kk:killed.add(root(kk['Assign'][0]))
      for tag in ['StorageLive','StorageDead']:
       if tag in kk:killed.add(kk[tag])
      if 'Call'in kk:killed.add(root(kk['Call']['call'].get('dest',{})))
      if 'Drop'in kk:killed.add(root(kk['Drop']['place']))
     if 'Move'in x:killed.add(root(x['Move']))
    stable={slot:val for slot,val in values.items()if slot not in killed}
    stable_bounds={key:val for key,val in bounds.items()if key in stable.values()}
    if stable_bounds:frames.append(dict(loop=sid,locals=stable,bounds=list(stable_bounds.items()),killed=sorted(x for x in killed if x is not None)))
    block(k['Loop'],stable,stable_bounds,sid)
    values=stable;bounds=stable_bounds
   elif any(t in k for t in ['Break','Continue','Abort']):return {},{},False
   else:values.clear();bounds.clear()
  return values,bounds,True
 if body and 'Structured'in body:block(body['Structured']['body'],{},{},-1)
 elif body and 'statements'in body:block(body,{},{},-1)
 return rows,frames
