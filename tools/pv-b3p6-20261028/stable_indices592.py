"""Computed private scalars survive a nested loop only when their stack slot
is never written/moved/dropped or mutably/raw borrowed by that entire loop.
Shared primitive usize captures cannot write their referent.
"""
from pathlib import Path
import json,lzma,copy,hashlib,argparse
from stable_arithmetic_collect592 import collect
from source_normalize583 import constants,normalize
from computed_indices583 import render
from initializer_source578 import find
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def scan(ll):
 fs={f['def_id']:f for f in ll['fun_decls']if f};vs,_=constants(ll,fs);b,changes=normalize(fs[218]['body'],vs)
 rows=[r for r in collect(b)if r['statement']==29777];assert len(rows)<=1
 return rows,changes

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];g=json.loads((I/'direct3-instantiated-callcone.json').read_text());rows,changes=scan(ll);assert len(rows)==1;controls={}
 for label,k in{
 'outer_scalar_overwritten':{'Assign':[{'kind':{'Local':5}},{'Use':[{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','16']}}}}},'Yes']}]},
 'outer_address_escaped':{'Assign':[{'kind':{'Local':999}},{'RawPtr':{'place':{'kind':{'Local':5}}}}]},
 'inner_scalar_mutably_borrowed':{'Assign':[{'kind':{'Local':999}},{'Ref':{'place':{'kind':{'Local':21}},'kind':'Mut'}}]},
 }.items():
  changed=copy.deepcopy(ll);f=next(f for f in changed['fun_decls']if f and f['def_id']==218);loop=find(f['body'],11944)['kind']['Loop'];loop['statements'].insert(0,dict(id=-1,kind=k));rs,_=scan(changed);assert not rs;controls[label]='no guard emitted'
 name='PV_B3P_StableIndices592227';s='import PV_B3P_ArithmeticEvents583227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n'
 for j,r in enumerate(rows):
  inst=next(k for k,v in g['instances'].items()if v['id']==218);r.update(instance=inst,function_id=218,lemma=name+f'.certificate_{j}');inputs=[];expr=render(r['expression'],inputs);assert len(inputs)==2;args=f'{expr} {r["slack"]} effects'
  s+=f'''/-- Exact source 4*outer+inner at {inst}:{r['statement']}. -/
def sourceState_{j} (input0 input1 : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_ArithmeticEvents583227.sourceEvent {args}
theorem certificate_{j} {{α : Type}} (input0 input1 : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_{j} input0 input1 effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_ArithmeticEvents583227.event_certificate {args} observed ran normal first second
#print axioms certificate_{j}
'''
 fs={f['def_id']:f for f in ll['fun_decls']if f};x=dict(rows=rows,count=1,chunks=[name],normalizations=changes,body_sha256=sha(json.dumps(fs[218]['body'],sort_keys=True).encode()),llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 nested private arithmetic scalar frame and read-only usize capture plus named kernel guard',validation_status='PREPARATION; compile and raw audit required',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',native_borrow_restoration=False,whole_caller_association=False,premises_removed=[])
 for p,t in {D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'STABLE-INDICES-D592.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(count=1,controls=controls,check=a.check)))
if __name__=='__main__':main()
