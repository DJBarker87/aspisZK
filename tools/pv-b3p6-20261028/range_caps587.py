"""Bind fixed-end private Range constructors and next-restoration frames.

Each range's only borrowed access in its loop must be the checked .next
prefix. No raw pointer, field write, copied range, or escaped borrow is allowed.
The Some arm must follow next immediately, with the None arm breaking.
This supplies actual constructor/end frames for the source next bound law.
"""
from pathlib import Path
import argparse,copy,hashlib,json,lzma
from initializer_source578 import compact,find
from frame_indices578 import root,dicts
from dominated_indices578 import collect
from specialized_indices578 import instantiate
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def seeds(body):
 found={};frames=[]
 def op(o,ranges):
  for tag in ('Move','Copy'):
   if tag in o and 'Local'in o[tag]['kind']:return ranges.get(root(o[tag]))
 def walk(b,incoming):
  ranges=dict(incoming)
  for st in b['statements']:
   sid=st['id'];k=st['kind']
   if not isinstance(k,dict):ranges.clear();continue
   if 'Assign'in k:
    dest,rhs=k['Assign'];value=op(rhs['Use'][0],ranges)if 'Use'in rhs else None
    if 'Aggregate'in rhs:
     tag,fields=rhs['Aggregate']
     if tag.get('Adt',[{}])[0].get('id')=={'Adt':25}and len(fields)==2 and 'Const'in fields[1] and literal(fields[1]['Const'])is not None:
      value=dict(start=literal(fields[0]['Const'])if 'Const'in fields[0]else None,start_operand=copy.deepcopy(fields[0]),end=literal(fields[1]['Const']),constructor=sid)
    for x in dicts(rhs):
     if 'Move'in x:ranges.pop(root(x['Move']),None)
    ranges.pop(root(dest),None)
    if 'Local'in dest['kind']and value:ranges[root(dest)]=value
   elif 'Call'in k:
    call=k['Call']['call'];kind=call['func'].get('Regular',{}).get('kind',{}).get('Fun',{});value=op(call['args'][0],ranges)if kind=={'Regular':37}and len(call['args'])==1 else None
    for x in dicts(call['args']):
     if 'Move'in x:ranges.pop(root(x['Move']),None)
    ranges.pop(root(call.get('dest',{})),None)
    if value:ranges[root(call['dest'])]=value
   elif 'StorageLive'in k or 'StorageDead'in k:ranges.pop(next(iter(k.values())),None)
   elif 'Loop'in k:
    loop=k['Loop'];prefix=[];aliases={};selected=None;ref_ids=set()
    for q in loop['statements']:
     kk=q['kind'];prefix.append(q)
     if not isinstance(kk,dict):break
     if 'Assign'in kk:
      dest,rhs=kk['Assign']
      if 'Ref'in rhs:
       p=rhs['Ref']['place'];r=root(p)
       if p['kind'].get('Local')in ranges:aliases[root(dest)]=root(p);ref_ids.add(q['id'])
       elif 'Projection'in p['kind']and p['kind']['Projection'][1]=='Deref'and r in aliases:aliases[root(dest)]=aliases[r];ref_ids.add(q['id'])
     if 'Call'in kk:
      c=kk['Call']['call'];fid=c['func'].get('Regular',{}).get('kind',{}).get('Fun',{})
      if fid!={'Regular':38}or len(c['args'])!=1:break
      arg=c['args'][0];a=next(iter(arg.values()));it=aliases.get(root(a));opt=root(c['dest'])
      if it not in ranges:break
      selected=(q['id'],it,opt,dict(aliases));continue
     if 'Switch'in kk:
      if not selected:break
      variant=kk['Switch'].get('Match')
      if not variant:break
      place,arms,default=variant;callid,it,opt,alias=selected
      if place['kind']!={'Local':opt}or default is not None or len(arms)!=2 or arms[0][0]!=[0]or arms[1][0]!=[1]or arms[1][1]['statements']:break
      none=arms[0][1]['statements']
      if not none:break
      terminal=none[-1]['kind']
      if not (isinstance(terminal,dict)and any(tag in terminal for tag in ['Break','Continue','Abort']))and terminal not in ['Return','UnwindResume']:break
      # Every access to the private range/borrow aliases is in this prefix;
      # subsequent effect code gets no access to their stack locations.
      allowed={p['id']for p in prefix};safe=True
      for x in dicts(loop):
       if 'id'not in x or 'span'not in x or 'kind'not in x:continue
       xx=x['kind']
       if not isinstance(xx,dict):continue
       if 'Assign'in xx:
        dest,rhs=xx['Assign']
        if root(dest)==it or(root(dest)in alias and x['id']not in ref_ids):safe=False
        if any(root(n[tag])in ({it}|set(alias))for n in dicts(rhs)for tag in ('Move','Copy')if tag in n):safe=False
        for tag in ('Ref','RawPtr'):
         if tag in rhs and root(rhs[tag]['place'])in({it}|set(alias))and(tag=='RawPtr'or x['id']not in ref_ids):safe=False
       if 'Call'in xx and x['id']!=callid:
        if any(root(n[tag])in({it}|set(alias))for n in dicts(xx['Call']['call']['args'])for tag in ('Move','Copy')if tag in n):safe=False
       if 'Drop'in xx and root(xx['Drop']['place'])in({it}|set(alias)):safe=False
      # Fresh stack privacy must also exclude a borrow that escaped BEFORE
      # the loop; checking only the loop body would miss that capability.
      for x in dicts(body):
       if 'id'not in x or 'span'not in x or not isinstance(x.get('kind'),dict):continue
       xx=x['kind']
       if 'Assign'in xx:
        rhs=xx['Assign'][1]
        for tag in ('Ref','RawPtr'):
         if tag in rhs and root(rhs[tag]['place'])==it and(tag=='RawPtr'or x['id']not in ref_ids):safe=False
      if safe:
       bound=ranges[it]['end'];found[q['id']]=(opt,bound,callid)
       frames.append(dict(loop=sid,iterator_local=it,next_statement=callid,match_statement=q['id'],option_local=opt,constructor=ranges[it],borrow_aliases=alias,source_prefix=compact(prefix),source_loop_sha256=sha(json.dumps(loop,sort_keys=True).encode()),range_end_lemma='PV_B3P_RangeEvents578227.next_end',source_end_invariant_lemma='PV_B3P_RangeEvents578227.private_end_invariant'))
      break
    walk(loop,{})
    ranges.clear()
   elif 'Switch'in k:
    tag,v=next(iter(k['Switch'].items()))
    branches=v[1:]if tag=='If'else[b for _,b in v[1]]+([v[2]]if v[2]else[])if tag=='Match'else[b for _,b in v[2]]+([v[3]]if v[3]else[])
    for child in branches:walk(child,{})
    ranges.clear()
   else:ranges.clear()
 if body and 'Structured'in body:walk(body['Structured']['body'],{})
 return found,frames
