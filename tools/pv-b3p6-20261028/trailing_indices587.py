"""Generate source nonzero-loop cttz guards; zero is retained as a skip branch."""
from pathlib import Path
import argparse,json,lzma,hashlib,copy
from initializer_source578 import compact,find
from fixed_indices572 import literal
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def certify(fs,t):
 assert compact(fs[397]['body'])==t
 # The tested current mask is snapshotted again for the source cttz call;
 # neither the incoming mask nor an old iteration's mask is substituted.
 assert compact(find(fs[397]['body'],25464)['kind']['Assign'][1]['BinaryOp'])==['Ne',{'Move':{'kind':{'Local':11}}},{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['U16','0']}}}}}]
 for sid in[25463,25469]:assert compact(find(fs[397]['body'],sid)['kind']['Assign'][1]['Use'][0])=={'Copy':{'kind':{'Local':2}}}
 c=find(fs[397]['body'],25476)['kind']['Call']['call'];assert c['func']['Regular']['kind']['Fun']=={'Regular':465}and compact(c['args'])==[{'Move':{'kind':{'Local':14}}}]
 cast=find(fs[397]['body'],25478)['kind']['Assign'][1]['UnaryOp'];assert compact(cast)==[{'Cast':{'Scalar':[{'UInt':'U32'},{'UInt':'Usize'}]}},{'Move':{'kind':{'Local':13}}}]
 guard=find(fs[397]['body'],25537)['kind']['Switch']['If'];assert compact(guard[0])=={'Move':{'kind':{'Local':10}}}and guard[2]['statements'][-1]['kind']=={'Break':0}
 for sid in[30838,30843]:
  call=find(fs[397]['body'],sid)['kind']['Call']['call'];assert literal(call['func']['Regular']['generics']['const_generics'][0])==16
 return dict(mask_test=25464,guard_branch=25537,cttz_call=25476,cttz_cast=25478,source_mask_local=2,index_local=12,index_sites=[30838,30843],intrinsic_source_law='PV_B3P_MaskSource542227.trailing_zeros_source_step542',intrinsic_bound='PV_B3P_MaskSource542227.cttz16_nonzero_bound542',compiler_boundary='V370 / D381 / D386 retained')
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());t=json.loads((R/'TRAILING-TEMPLATE-D587.json').read_text());binding=certify(fs,t);controls={}
 for sid,label in[(25464,'missing_nonzero_test'),(25476,'wrong_intrinsic_operand'),(25478,'wrong_cast')]:
  changed=copy.deepcopy(fs);find(changed[397]['body'],sid)['kind']={'StorageDead':999}
  try:certify(changed,t)
  except(AssertionError,KeyError):controls[label]='rejected'
  else:raise AssertionError(label)
 name='PV_B3P_TrailingIndices587227';s='import PV_B3P_TrailingEvents587227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_TrailingEvents587227\nset_option autoImplicit false\n';inst=next(k for k,v in g['instances'].items()if v['id']==397);rows=[]
 for sid in[30838,30843]:
  label=f'certificate_{sid}';rows.append(dict(instance=inst,function_id=397,statement=sid,lemma=name+'.'+label))
  s+=f'''/-- Actual source nonzero-loop cttz observation at {inst}:{sid}. -/
theorem {label} {{α : Type}} (bits : BitVec 16) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent bits effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate bits effects observed ran normal first second
#print axioms {label}
'''
 x=dict(rows=rows,count=2,chunks=[name],binding=binding,llbc_sha256=sha(raw),negative_controls=controls,validation_status='PREPARATION; focused Lean compiles and raw NEP audit pending',evidence_class='SCRIPT-CHECKED own-1 actual nonzero source mask/cttz/cast projections plus named kernel guards; intrinsic under V370',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',whole_caller_association=False,premises_removed=[])
 for p,s in{D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'TRAILING-INDICES-D587.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=2,check=a.check,controls=controls)))
if __name__=='__main__':main()
