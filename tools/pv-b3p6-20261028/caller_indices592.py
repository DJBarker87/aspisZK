"""Bind helper scalar indices to every actual incoming caller's argument
expressions. Caller comparison tests are kept as expression observations;
no helper-domain hypothesis is added to the endpoint.
"""
from pathlib import Path
import json,lzma,copy,hashlib,argparse
from scalar_constants592 import constants,REV
from caller_observe592 import collect
from source_normalize583 import normalize
from range_indices578 import seeds
from shared_scalar_collect587 import collect as flow
from initializer_source578 import compact,find
from computed_indices583 import render
from frame_indices578 import dicts
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def observations(ll,g):
 fs={f['def_id']:f for f in ll['fun_decls']if f};vs,bindings=constants(ll,fs);obs={15:[],39:[],240:[]}
 for fid in[7,14,58]:
  b,changes=normalize(fs[fid]['body'],vs);sd,_=seeds(b)
  for r in collect(b,sd):
   if r['callee']in obs:obs[r['callee']].append(dict(caller_id=fid,normalizations=changes,**r))
 for callee,rs in obs.items():
  assert len(rs)=={15:6,39:3,240:8}[callee]
  assert len([e for e in g['edges']if e['callee_id']==callee])==len(rs)
  assert sorted(int(e['caller'].split(':')[0])for e in g['edges']if e['callee_id']==callee)==sorted(r['caller_id']for r in rs)
 b,_=normalize(fs[7]['body'],vs);rs,_=flow(b);fixed=[r for r in rs if r['statement']==29213];assert len(fixed)==1
 return obs,bindings,fixed

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());obs,bindings,fixed=observations(ll,g);template=json.loads((R/'CALLER-TEMPLATE-D592.json').read_text())
 for fid in[15,39,240]:assert compact(fs[fid]['body'])==template[str(fid)]
 controls={}
 for fid,sid,label in[(7,970,'mask_column_test_changed'),(14,2082,'root_caller_changed'),(58,6813,'digest_start_changed')]:
  changed=copy.deepcopy(ll);f=next(f for f in changed['fun_decls']if f and f['def_id']==fid)
  if label=='root_caller_changed':sid=next(r['statement']for r in obs[39]if r['caller_id']==14)
  find(f['body'],sid)['kind']={'StorageDead':999}
  try:
   oo,_,ff=observations(changed,g)
   assert oo==obs and ff==fixed
  except(AssertionError,KeyError):controls[label]='rejected or changed source event'
  else:raise AssertionError(label)
 name='PV_B3P_CallerIndices592227';s='import PV_B3P_RangeComputedEvents592227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n';rows=[]
 for callee,site,length in[(15,29259,84),(39,29305,21),(240,30468,16)]:
  inst=next(k for k,v in g['instances'].items()if v['id']==callee);lemmas=[]
  for j,r in enumerate(obs[callee]):
   if callee==15:
    point,column=r['arguments'][1:];assert point and column
    expr=dict(op='add',left=dict(op='mul',left=point['expression'],right=dict(op='literal',value=28)),right=column['expression']);limit=(point['limit']-1)*28+column['limit']
   elif callee==39:expr=r['arguments'][0]['expression'];limit=r['arguments'][0]['limit']
   else:
    start=r['arguments'][3];assert start and start['expression']['op']=='literal'
    expr=dict(op='add',left=start['expression'],right=dict(op='bounded',input=['snapshot','actual_range_next',240],limit=8));limit=start['limit']+7
   range_limit=None
   for node in dicts(expr):
    if node.get('op')=='bounded' and node['input'][0]=='rangeItem':
     assert range_limit in[None,node['limit']];range_limit=node['limit'];node['input']=['snapshot','actual_range_next',callee]
   assert limit<=length;inputs=[];text=render(expr,inputs);label=f'certificate_{callee}_{j}';lemmas.append(name+'.'+label);params=' '.join('input'+str(k)for k in range(len(inputs)));binder=f'({params} : Nat)'if inputs else''
   if callee==240 or range_limit is not None:
    range_limit=8 if callee==240 else range_limit
    assert inputs==[json.dumps(['snapshot','actual_range_next',callee])];text=text.replace('input0','item.val');binder='(handler : Str → Result Never) (start : Usize)';args=f'handler ⟨start,{range_limit}#usize⟩ (fun item => {text}) {length-limit} effects';ns='PV_B3P_RangeComputedEvents592227'
   else:args=f'{text} {length-limit} effects';ns='PV_B3P_ArithmeticEvents583227'
   s+=f'''/-- Actual incoming {r['caller_id']}:{r['statement']} -> {inst}:{site}. -/
theorem {label} {{α : Type}} {binder} (effects : List (Result Unit))
    (observed : IndexState) (ran : {ns}.sourceEvent {args} = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  {ns}.event_certificate {args} observed ran normal first second
#print axioms {label}
'''
  rows.append(dict(instance=inst,function_id=callee,statement=site,lemma=lemmas[0],all_caller_lemmas=lemmas,actual_incoming=obs[callee]))
 r=fixed[0];inst=next(k for k,v in g['instances'].items()if v['id']==7);label='mask_column';rows.append(dict(instance=inst,function_id=7,statement=29213,lemma=name+'.'+label,binding=r));s+=f'''theorem {label} {{α : Type}} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState)
    (ran : PV_B3P_DominatedEvents578227.sourceEvent 10 0 index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate 10 0 index effects observed ran normal first second
#print axioms {label}
'''
 x=dict(rows=rows,count=4,chunks=[name],scalar_constants=bindings,llbc_sha256=sha(raw),helper_templates='CALLER-TEMPLATE-D592.json',negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 all incoming caller scalar-domain and helper arithmetic projections plus named kernel guards',validation_status='PREPARATION; compile and raw audit required',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',whole_caller_association=False,premises_removed=[])
 for p,t in{D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'CALLER-INDICES-D592.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(count=4,caller_cases=sum(len(rs)for rs in obs.values()),check=a.check,controls=controls)))
if __name__=='__main__':main()
