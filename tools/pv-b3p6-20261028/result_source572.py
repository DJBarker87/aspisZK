"""Check the exact uninhabited-success residual carrier, not a success premise."""
from pathlib import Path
import argparse,hashlib,json,lzma
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031'
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];table={}
 def scan(v):
  if isinstance(v,dict):
   if 'HashConsedValue'in v:
    n,x=v['HashConsedValue'];table[n]=x
   for x in v.values():scan(x)
  elif isinstance(v,list):
   for x in v:scan(x)
 scan(ll)
 def resolve(v):
  while isinstance(v,dict)and ('Deduplicated'in v or 'HashConsedValue'in v):v=table[v['Deduplicated']]if 'Deduplicated'in v else v['HashConsedValue'][1]
  return v
 f=next(f for f in ll['fun_decls']if f and f['def_id']==10)
 sig=resolve(f['signature']['inputs'][0]);result=sig['Adt'];assert result['id']=={'Adt':3}
 first=resolve(result['generics']['types'][0]);empty=next(t for t in ll['type_decls']if t and t['def_id']==first['Adt']['id']['Adt'])
 assert empty['kind']=={'Enum':[]},empty['kind']
 # Exact straight-line prefix through the MIR assertion; no hidden effects.
 body=f['body']['Structured']['body']['statements'];end=next(i for i,s in enumerate(body)if s['id']==1718);prefix=body[:end+1]
 semantic=[s for s in prefix if not any(k in s['kind']for k in ['StorageLive','StorageDead'])]
 assert [s['id']for s in semantic]==[1715,1716,1718]
 p,rhs=semantic[0]['kind']['Assign'];assert p['kind']=={'Local':2}and rhs['Discriminant']['kind']=={'Local':1}
 p,rhs=semantic[1]['kind']['Assign'];op,l,r=rhs['BinaryOp'];assert p['kind']=={'Local':5}and op=='Eq'and l['Copy']['kind']=={'Local':2}and r['Const']['kind']['Literal']['Scalar']['Signed']==['Isize','1']
 test=semantic[2]['kind']['Assert']['assert'];assert test['cond']['Move']['kind']=={'Local':5}and test['expected']is True
 graph=json.loads((I/'direct3-instantiated-callcone.json').read_text());instances=[dict(instance=k,environment=v['environment'],statement=1718)for k,v in graph['instances'].items()if v['id']==10];assert len(instances)==2
 s='''import PV_B3P_PanicPatterns571227
namespace PV_B3P_ResultSource572227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Exact input shape Result<Infallible,E>; E remains arbitrary. -/
def discriminant {E : Type} : core.result.Result Empty E → Nat
  | .Ok _ => 0
  | .Err _ => 1

def sourceCondition {E : Type} (r : core.result.Result Empty E) : Bool :=
  discriminant r == 1

theorem source_guard {E : Type} (r : core.result.Result Empty E) :
    sourceCondition r = true := by
  cases r with
  | Ok impossible => exact Empty.elim impossible
  | Err _ => rfl

/-- Both actual specializations use the same source input carrier shape. -/
theorem family_certificate {E α : Type} (_site : Fin 2)
    (r : core.result.Result Empty E) (normal first second : Result α) :
    ¬ diagnostic (sourceCondition r = true) ∧
      branch (sourceCondition r = true) normal first =
        branch (sourceCondition r = true) normal second :=
  (assertion (sourceCondition r) true normal first second).2 (source_guard r)
#print axioms source_guard
#print axioms family_certificate
end PV_B3P_ResultSource572227
'''
 x=dict(llbc_sha256=sha(raw),input_signature=f['signature'],resolved_residual_type=sig,uninhabited_type=empty,prefix=prefix,instances=instances,source_state_projection='input Result<Infallible,E> discriminant, compare against Err tag 1',generic_module_sha256=sha(s.encode()),evidence_class='script-checked LLBC typed local-state binding and Lean uninhabited-carrier guard',deployed_std_source_parity=dict(status='token identity checked',record='RESULT-SOURCE-PARITY-D572.json',sha256=sha((R/'RESULT-SOURCE-PARITY-D572.json').read_bytes()))if (R/'RESULT-SOURCE-PARITY-D572.json').exists()else 'OPEN until result.rs parity is recorded',whole_source_cone_complete=False,premises_removed=[])
 for p,t in {D/'lean/PV_B3P_ResultSource572227.lean':s,R/'RESULT-SOURCE-GUARDS-D572.json':json.dumps(x,indent=2)+'\n'}.items():
  if args.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(result_residual_sites=2,empty_type_id=empty['def_id'],check=args.check)))
if __name__=='__main__':main()
