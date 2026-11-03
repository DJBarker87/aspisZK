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
     if tag.get('Adt',[{}])[0].get('id')=={'Adt':25}and len(fields)==2 and all('Const'in o and literal(o['Const'])is not None for o in fields):
      value=dict(start=literal(fields[0]['Const']),end=literal(fields[1]['Const']),constructor=sid)
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
      if len(none)!=1 or none[0]['kind']!={'Break':0}:break
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

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());prior=json.loads((R/'SOURCE-COVERAGE-D572.json').read_text());already={(r['instance'],r['statement'])for v in prior['groups'].values()for r in v['certified']}
 for n in ['INITIALIZER-SOURCE','FRAME-INDICES','SLICE-SOURCE','DOMINATED-INDICES','SPECIALIZED-INDICES']:already.update((r['instance'],r['statement'])for r in json.loads((R/(n+'-D578.json')).read_text())['rows'])
 # Bind into_iter identity and next forwarding rather than trusting names.
 identity=compact(fs[37]['body']['Structured']['body']['statements']);assert[(x['id'],x['kind'])for x in identity]==[(3719,{'StorageLive':0}),(3720,{'Assign':[{'kind':{'Local':0}},{'Use':[{'Move':{'kind':{'Local':1}}},'Yes']}]}),(3721,{'StorageDead':1}),(3722,'Return')]
 forwarded=fs[38]['body']['Structured']['body']['statements'];c=forwarded[1]['kind']['Call']['call'];assert c['func']['Regular']['kind']['Fun']=={'Regular':186}and c['args'][0]['Move']['kind']=={'Local':1}and c['dest']['kind']=={'Local':0}
 assert len(forwarded)==4 and compact(forwarded[0]['kind'])=={'StorageLive':0}and compact(forwarded[2]['kind'])=={'StorageDead':1}and forwarded[-1]['kind']=='Return'and len(c['args'])==1
 for v in g['instances'].values():
  if v['id']==38:assert v['environment']['types']==[{'Literal':{'UInt':'Usize'}}]
 rows=[];bindings=[];control_fixture=None
 for inst,v in g['instances'].items():
  f=fs[v['id']];body=f.get('body')
  if not body:continue
  subst=[];body=instantiate(body,v['environment']['const_generics'],subst)if v['environment']['const_generics']else body
  source_seeds,frames=seeds(body)
  if not source_seeds:continue
  if control_fixture is None:control_fixture=(copy.deepcopy(body),frames[0])
  bindings.append(dict(instance=inst,frames=frames,source_body_sha256=sha(json.dumps(f['body'],sort_keys=True).encode()),substitutions=subst))
  nexts={v[2]for v in source_seeds.values()}
  for row in collect(body,source_seeds):
   if row['predicate_statement']not in nexts or(inst,row['statement'])in already:continue
   rows.append(dict(instance=inst,environment=v['environment'],**row));already.add((inst,row['statement']))
 controls={}
 sample,frame=control_fixture;loopid=frame['loop'];matchid=frame['match_statement'];it=frame['iterator_local'];callid=frame['next_statement'];alias=next(iter(frame['borrow_aliases']))
 def inject(body,statement):
  b=find(body,loopid)['kind']['Loop']['statements'];position=next(i for i,x in enumerate(b)if x['id']==callid);b.insert(position,statement)
 edits={
  'unknown_call_before_next':lambda b:inject(b,dict(id=-1,span={},kind={'Call':{'call':{'func':{},'args':[],'dest':{'kind':{'Local':999}}}}})),
  'borrow_copy_escape':lambda b:inject(b,dict(id=-1,span={},kind={'Assign':[{'kind':{'Local':999}},{'Use':[{'Copy':{'kind':{'Local':alias}}},'Yes']}]})),
  'raw_range_address':lambda b:inject(b,dict(id=-1,span={},kind={'Assign':[{'kind':{'Local':999}},{'RawPtr':{'place':{'kind':{'Local':it}},'kind':'Mut'}}]})),
  'private_range_overwrite':lambda b:find(b,loopid)['kind']['Loop']['statements'].append(dict(id=-1,span={},kind={'Assign':[{'kind':{'Local':it}},{'Use':[{'Const':{}},'Yes']}]})),
  'none_arm_does_not_break':lambda b:find(b,matchid)['kind']['Switch']['Match'][1][0][1]['statements'][0].__setitem__('kind','Nop'),
  'different_next':lambda b:find(b,callid)['kind']['Call']['call']['func']['Regular']['kind']['Fun'].__setitem__('Regular',999),
 }
 for label,edit in edits.items():
  changed=copy.deepcopy(sample);edit(changed);assert matchid not in seeds(changed)[0],label;controls[label]='no range frame emitted'
 # A pre-loop escape must be rejected even though the loop itself is intact.
 changed=copy.deepcopy(sample)
 def preescape(x):
  if isinstance(x,dict):
   if 'statements'in x:
    for j,st in enumerate(x['statements']):
     if st['id']==loopid:
      x['statements'].insert(j,dict(id=-1,span={},kind={'Assign':[{'kind':{'Local':999}},{'Ref':{'place':{'kind':{'Local':it}},'kind':'Mut'}}]}));return True
   for v in list(x.values()):
    if preescape(v):return True
  elif isinstance(x,list):
   for v in list(x):
    if preescape(v):return True
  return False
 assert preescape(changed);assert matchid not in seeds(changed)[0];controls['pre_loop_address_escape']='no range frame emitted'
 outputs={};chunks=[]
 for offset in range(0,len(rows),24):
  name=f'PV_B3P_RangeIndices578227_{offset//24:02d}';chunks.append(name)
  s='import PV_B3P_RangeEvents578227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_RangeEvents578227\nset_option autoImplicit false\n'
  for j,row in enumerate(rows[offset:offset+24],offset):
   row['lemma']=name+f'.certificate_{j}';limit,slack=row['limit'],row['slack']
   s+=f'''/-- Instance {row['instance']}, instruction {row['statement']}, next call {row['predicate_statement']}. -/
def sourceState_{j} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) :
    Result (Option IndexState) := sourceEvent handler ⟨start,{limit}#usize⟩ {slack} effects
theorem certificate_{j} {{α : Type}} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_{j} handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate handler ⟨start,{limit}#usize⟩ {slack} effects observed ran normal first second
#print axioms certificate_{j}
'''
  s+='end '+name+'\n';outputs[D/'lean'/(name+'.lean')]=s
 meta=dict(llbc_sha256=sha(raw),rows=rows,count=len(rows),chunks=chunks,negative_controls=controls,private_range_bindings=bindings,evidence_class='script-checked own-1 literal-end Range constructor/borrow frames plus Lean next output/end-restoration laws and generated event guards',source_next_binding='PV_B3P_NextFormatting569227.binding/model_binding; strict source specialization checked by STEP-SOURCE-GUARDS-D572.json',native_pointer_validity=False,array_element_restoration=False,whole_caller_association=False,premises_removed=[])
 outputs[R/'RANGE-INDICES-D578.json']=json.dumps(meta,indent=2)+'\n'
 for p,t in outputs.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(new_indices=len(rows),range_frames=sum(len(b['frames'])for b in bindings),chunks=chunks,check=a.check)))
if __name__=='__main__':main()
