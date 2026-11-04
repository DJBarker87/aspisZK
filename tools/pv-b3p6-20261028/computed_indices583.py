"""Generate guards for continuing strict-test paths and scalar arithmetic."""
from pathlib import Path
import argparse,json,lzma,hashlib,copy
from source_normalize583 import constants,normalize
from specialized_indices578 import instantiate
from range_indices578 import seeds
from flow_collect583 import collect as flow
from arithmetic_collect583 import collect as arithmetic
from initializer_source578 import find
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def render(e,inputs):
 op=e['op']
 def variable(snapshot):
  key=json.dumps(snapshot,sort_keys=True)
  if key not in inputs:inputs.append(key)
  return 'input'+str(inputs.index(key))
 if op=='literal':return f"(.literal {e['value']})"
 if op=='bounded':
  assert e['input'][0]=='snapshot','iterator-derived arithmetic needs an explicit source next event'
  return f"(.bounded {variable(e['input'])} {e['limit']})"
 if op=='remainder':return f"(.remainder {variable(e['input'])} {e['divisor']})"
 if op=='bitAnd':return f"(.bitAnd {variable(e['input'])} {e['mask']})"
 if op in ['add','mul']:return f"(.{op} {render(e['left'],inputs)} {render(e['right'],inputs)} (UScalar.size .Usize))"
 assert op=='quotient';return f"(.quotient {render(e['input'],inputs)} {e['divisor']})"

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());prior=json.loads((R/'SOURCE-COVERAGE-D580.json').read_text());remaining={(r['instance'],r['statement'])for v in prior['groups'].values()for r in v['remaining']};remaining-={(r['instance'],r['statement'])for r in json.loads((R/'NORMALIZED-INDICES-D583.json').read_text())['rows']};vs,_=constants(ll,fs);rows=[];sources=[]
 for inst,v in g['instances'].items():
  original=fs[v['id']].get('body')
  if not isinstance(original,dict):continue
  subst=[];body=instantiate(original,v['environment']['const_generics'],subst)if v['environment']['const_generics']else original;body,changes=normalize(body,vs);sd,ff=seeds(body);nexts={v[2]for v in sd.values()};new=[]
  for route,rs in [('flow',flow(body,sd)),('arithmetic',arithmetic(body,sd))]:
   for r in rs:
    if(inst,r['statement'])not in remaining:continue
    remaining.remove((inst,r['statement']));r=dict(instance=inst,function_id=v['id'],route='range'if route=='flow'and r['predicate_statement']in nexts else route,**r);rows.append(r);new.append(r['statement'])
  if new:sources.append(dict(instance=inst,original_sha256=sha(json.dumps(original,sort_keys=True).encode()),normalizations=changes,const_substitutions=subst,range_frames=ff,statements=new))
 controls={}
 # Actual dot loop: only its failure-side Break makes the continuation guarded.
 original=fs[9]['body'];body,_=normalize(original,vs)
 assert {29229,29234}<={r['statement']for r in flow(body)}
 changed=copy.deepcopy(body);test=find(changed,1644)['kind']['Switch']['If'];test[2]['statements']=[]
 assert not {29229,29234}&{r['statement']for r in flow(changed)};controls['removed_false_branch_break']='no guard emitted'
 # Swapping success/failure conditions cannot preserve the bound.
 changed=copy.deepcopy(body);find(changed,1641)['kind']['Assign'][1]['BinaryOp'][0]='Ge'
 assert not {29229,29234}&{r['statement']for r in flow(changed)};controls['opposite_continuation_predicate']='no guard emitted'
 body,_=normalize(fs[1]['body'],vs);assert{29177,29182}<={r['statement']for r in arithmetic(body)}
 for sid,label in [(89,'zero_divisor'),(98,'zero_remainder_divisor')]:
  changed=copy.deepcopy(body);find(changed,sid)['kind']['Assign'][1]['BinaryOp'][2]['Const']['kind']['Literal']['Scalar']['Unsigned'][1]='0'
  target=29177 if sid==89 else 29182
  assert target not in {r['statement']for r in arithmetic(changed)};controls[label]='no arithmetic guard emitted'
 changed=copy.deepcopy(body);find(changed,81)['kind']['Assign'][1]['BinaryOp'][2]['Const']['kind']['Literal']['Scalar']['Unsigned'][1]='85'
 assert 29177 not in {r['statement']for r in arithmetic(changed)};controls['quotient_input_exceeds_array_partition']='no arithmetic guard emitted'
 # Bit-and replacement by OR cannot inherit the mask bound.
 changed,_=normalize(fs[61]['body'],vs);find(changed,7387)['kind']['Assign'][1]['BinaryOp'][0]='BitOr'
 assert 29604 not in{r['statement']for r in arithmetic(changed)};controls['mask_operation_changed']='no arithmetic guard emitted'
 name='PV_B3P_ComputedIndices583227';s='import PV_B3P_ArithmeticEvents583227\nimport PV_B3P_RangeEvents578227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n'
 for j,r in enumerate(rows):
  r['lemma']=name+f'.certificate_{j}';route=r['route'];limit,slack=r['limit'],r['slack']
  if route=='arithmetic':
   ns='PV_B3P_ArithmeticEvents583227';inputs=[];expression=render(r['expression'],inputs);params='('+' '.join('input'+str(k)for k in range(len(inputs)))+' : Nat)';args=f"{expression} {slack} effects"
  elif route=='range':ns='PV_B3P_RangeEvents578227';params='(handler : Str → Result Never) (start : Usize)';args=f'handler ⟨start,{limit}#usize⟩ {slack} effects'
  else:ns='PV_B3P_DominatedEvents578227';params='(index : Nat)';args=f'{limit} {slack} index effects'
  s+=f'''/-- Instance {r['instance']}, scalar event {r['statement']}. -/
def sourceState_{j} {params} (effects : List (Result Unit)) : Result (Option IndexState) :=
  {ns}.sourceEvent {args}
theorem certificate_{j} {{α : Type}} {params} (effects : List (Result Unit))
    (observed : IndexState) (ran : {ns}.sourceEvent {args} = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  {ns}.event_certificate {args} observed ran normal first second
#print axioms certificate_{j}
'''
 outputs={D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'COMPUTED-INDICES-D583.json':json.dumps(dict(rows=rows,count=len(rows),chunks=[name],source_frames=sources,llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 continuing scalar control/operation projections plus kernel event certificates',whole_caller_association=False,native_pointer_validity='consumes shared pv-evhB4 owner relation when supplied; no separate owner relation constructed',premises_removed=[]),indent=2)+'\n'}
 for p,s in outputs.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=len(rows),routes={k:sum(r['route']==k for r in rows)for k in ['flow','range','arithmetic']},controls=controls,check=a.check)))
if __name__=='__main__':main()
