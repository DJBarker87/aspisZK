"""Bind every incoming StepBy::new step to source literal4, excluding zero.
No iterator value, allocation, drop, or specialization semantics is assumed.
"""
from pathlib import Path
import argparse,json,lzma,hashlib,copy,re
from initializer_source578 import find,compact,nodes
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def parity():
 from range_slice587 import body,tok
 expected='{ assert!(step != 0); let iter = <I as SpecRangeSetup<I>>::setup(iter, step); StepBy { iter, step_minus_one: step - 1, first_take: true } }'
 rows=[]
 for version in ['1.94.1','nightly-2026-06-01']:
  row=body(R/'std587-source'/version/'step_by.rs.xz','fn new(iter: I, step: usize)');assert tok(row['body'])==tok(expected);rows.append(dict(version=version,**row))
 return rows
def certify(fs,g,t):
 for fid in[96,439]:assert compact(fs[fid]['body'])==t[str(fid)]
 ins=[e for e in g['edges']if e['callee_id']==439];assert len(ins)==1 and ins[0]['caller'].startswith('96:')
 ins2=[e for e in g['edges']if e['callee_id']==96];assert len(ins2)==1 and ins2[0]['caller'].startswith('224:')
 calls=[]
 for st in nodes(fs[224]['body']):
  k=st['kind']
  if isinstance(k,dict)and'Call'in k:
   c=k['Call']['call']
   if c['func'].get('Regular',{}).get('kind',{}).get('Fun')=={'Regular':96}:calls.append(dict(statement=st['id'],call=compact(c)));assert literal(c['args'][1]['Const'])==4
 assert len(calls)==1 and calls[0]['statement']==13535
 c=find(fs[96]['body'],8964)['kind']['Call']['call'];assert c['func']['Regular']['kind']['Fun']=={'Regular':439}and compact(c['args'])==[{'Move':{'kind':{'Local':1}}},{'Move':{'kind':{'Local':2}}}]
 x=find(fs[439]['body'],26456)['kind']['Switch']['SwitchInt'];assert compact(x[0])=={'Copy':{'kind':{'Local':2}}}and len(x[2])==1 and compact(x[2][0][0])==[{'Scalar':{'Unsigned':['Usize','0']}}]and x[2][0][1]['statements']==[]and x[3]['statements'][-1]['kind']=='Return'
 assert 'Abort'in find(fs[439]['body'],26460)['kind']
 return dict(caller_edges=ins+ins2,calls=calls,forward=8964,zero_switch=26456,nonzero_arm_terminal=26455,panic_statement=26460)
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'STEP-PANIC-TEMPLATE-D587.json').read_text());binding=certify(fs,g,t);ps=parity();controls={}
 for fid,sid,label in[(224,13535,'zero_or_wrong_step'),(96,8964,'wrong_forwarding'),(439,26456,'wrong_source_zero_switch')]:
  changed=copy.deepcopy(fs);find(changed[fid]['body'],sid)['kind']={'StorageDead':999}
  try:certify(changed,g,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_StepPanic587227';s='''import PV_B3P_PanicPatterns571227
namespace PV_B3P_StepPanic587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Actual 224 ->96 ->439 scalar step; zero branch is the only path to26460. -/
def sourceCondition : Bool := decide (Nat.succ 3 ≠ 0)
theorem certificate {α : Type} (normal first second : Result α) :
    ¬ diagnostic (sourceCondition = true) ∧
      branch (sourceCondition = true) normal first = branch (sourceCondition = true) normal second :=
  (explicit_panic sourceCondition normal first second).2 (decide_eq_true (Nat.succ_ne_zero 3))
#print axioms certificate
end PV_B3P_StepPanic587227
'''
 inst=next(k for k,v in g['instances'].items()if v['id']==439);x=dict(rows=[dict(instance=inst,function_id=439,statement=26460,lemma=name+'.certificate')],count=1,chunks=[name],binding=binding,source_parity=ps,negative_controls=controls,llbc_sha256=sha(raw),validation_status='PREPARATION; focused Lean compile and raw NEP audit pending',evidence_class='SCRIPT-CHECKED own-1 literal incoming step/forward/control projection plus named kernel nonzero law',whole_caller_association=False,drop_and_specialization_association=False,premises_removed=[])
 for p,s in {D/'lean'/(name+'.lean'):s,R/'STEP-PANIC-D587.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_panics=1,check=a.check,controls=controls)))
if __name__=='__main__':main()
