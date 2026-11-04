"""Bind captured old Range1..16 index to the shifts[round-1] event."""
from pathlib import Path
import json,lzma,hashlib,argparse,copy
from initializer_source578 import compact,find
from source_normalize583 import constants,normalize
from range_caps587 import seeds
from capture_guards587 import chain
from callback_indices584 import source_chain
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def certify(ll,fs,g,t):
 for fid in[53,362,508]:assert compact(fs[fid]['body'])==t[str(fid)]
 source_chain(fs,json.loads((R/'CALLBACK-TEMPLATE-D584.json').read_text()));chains=chain(g,508,362)
 vs,_=constants(ll,fs);b,nn=normalize(fs[362]['body'],vs);sd,frames=seeds(b);frame=next(f for f in frames if f['next_statement']==24471);assert frame['constructor']['start']==1 and frame['constructor']['end']==16 and frame['iterator_local']==31
 assert compact(find(fs[362]['body'],24489)['kind']['Assign'][1]['Use'][0])=={'Copy':{'kind':{'Projection':[{'kind':{'Local':32}},{'Field':[{'Adt':[16,1]},0]}]}}}
 c=find(fs[362]['body'],24535)['kind']['Call']['call'];assert c['func']['Regular']['kind']['Fun']=={'Regular':53}and compact(c['args'])==[{'Move':{'kind':{'Local':41}}}]
 ag=compact(find(fs[362]['body'],24520)['kind']['Assign'][1]['Aggregate']);assert ag[0]['Adt'][0]['id']=={'Adt':113}and ag[1][2]=={'Move':{'kind':{'Local':44}}}
 ref=compact(find(fs[362]['body'],24519)['kind']['Assign'][1]['Ref']);assert ref['kind']=='Shared'and ref['place']['kind']=={'Local':35}
 assert compact(find(fs[508]['body'],28109)['kind']['Assign'][1]['Use'][0])=={'Copy':{'kind':{'Projection':[{'kind':{'Projection':[{'kind':{'Local':1}},'Deref']}},{'Field':[{'Adt':[113,None]},2]}]}}}
 assert compact(find(fs[508]['body'],28110)['kind']['Assign'][1]['Use'][0])=={'Copy':{'kind':{'Projection':[{'kind':{'Local':16}},'Deref']}}}
 assert compact(find(fs[508]['body'],28111)['kind']['Assign'][1]['BinaryOp'])==[{'Sub':'Wrap'},{'Move':{'kind':{'Local':13}}},{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','1']}}}}}]
 c=find(fs[508]['body'],31208)['kind']['Call']['call'];assert literal(c['func']['Regular']['generics']['const_generics'][0])==15 and compact(c['args'][-1])=={'Copy':{'kind':{'Local':12}}}
 return dict(source_chains=chains,normalizations=nn,range_frame=frame,old_index=24489,shared_capture=24519,closure_capture=24520,caller=24535,leaf_read=28110,wrapped_subtraction=28111,target=31208)
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'POSITIVE-RANGE-TEMPLATE-D587.json').read_text());binding=certify(ll,fs,g,t);controls={}
 for fid,sid,label in[(362,24438,'changed_range_entry'),(362,24519,'changed_capture'),(508,28111,'changed_subtraction')]:
  changed=copy.deepcopy(fs);find(changed[fid]['body'],sid)['kind']={'StorageDead':999}
  try:certify(ll,changed,g,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_PositiveRange587227';s='''import PV_B3P_PositiveRangeEvents587227
namespace PV_B3P_PositiveRange587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_PositiveRangeEvents587227
set_option autoImplicit false
/-- Actual old private Range1..16 counter, captured for source508:31208. -/
theorem certificate {α : Type} (n : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent n effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate n effects observed ran normal first second
#print axioms certificate
end PV_B3P_PositiveRange587227
''';inst=next(k for k,v in g['instances'].items()if v['id']==508);x=dict(rows=[dict(instance=inst,function_id=508,statement=31208,lemma=name+'.certificate')],count=1,chunks=[name],binding=binding,llbc_sha256=sha(raw),negative_controls=controls,validation_status='PREPARATION; focused Lean compiles and raw NEP audit pending',evidence_class='SCRIPT-CHECKED own-1 positive private range/capture/subtract projection plus named kernel invariant and guard',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',native_borrow_restoration=False,whole_caller_association=False,premises_removed=[])
 for p,s in{D/'lean'/(name+'.lean'):s,R/'POSITIVE-RANGE-D587.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=1,check=a.check,controls=controls)))
if __name__=='__main__':main()
