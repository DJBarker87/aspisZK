"""Generate source scalar guards carried through private nested-loop frames.
The entire loop is scanned for writes/moves/lifetime/drop and address escape.
No native reference restoration or caller association is inferred.
"""
from pathlib import Path
import argparse,json,lzma,hashlib,copy
from source_normalize583 import constants,normalize
from specialized_indices578 import instantiate
from range_indices578 import seeds
from flow_collect587 import collect
from initializer_source578 import find
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def scan(ll,g):
 fs={f['def_id']:f for f in ll['fun_decls']if f};vs,_=constants(ll,fs);remaining={(r['instance'],r['statement'])for v in json.loads((R/'SOURCE-COVERAGE-D584.json').read_text())['groups'].values()for r in v['remaining']};rows=[];sources=[]
 for inst,v in g['instances'].items():
  original=fs[v['id']].get('body')
  if not isinstance(original,dict):continue
  subst=[];b=instantiate(original,v['environment']['const_generics'],subst)if v['environment']['const_generics']else original;b,changes=normalize(b,vs);sd,rr=seeds(b);rs,ff=collect(b,sd);accepted=[]
  for r in rs:
   if(inst,r['statement'])not in remaining:continue
   remaining.remove((inst,r['statement']));r=dict(instance=inst,function_id=v['id'],route='range'if r['predicate_statement']in {q[2]for q in sd.values()}else'flow',**r);rows.append(r);accepted.append(r['statement'])
  if accepted:sources.append(dict(instance=inst,original_sha256=sha(json.dumps(original,sort_keys=True).encode()),normalizations=changes,const_substitutions=subst,range_frames=rr,nested_frames=ff,statements=accepted))
 return rows,sources

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];g=json.loads((I/'direct3-instantiated-callcone.json').read_text());rows,sources=scan(ll,g);assert len(rows)==7
 controls={};fs={f['def_id']:f for f in ll['fun_decls']if f}
 for label,kind in {
  'outer_scalar_overwritten':{'Assign':[{'kind':{'Local':11}},{'Use':[{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','9']}}}}},'Yes']}]},
  'outer_scalar_address_escapes':{'Assign':[{'kind':{'Local':999}},{'RawPtr':{'place':{'kind':{'Local':11}}}}]},
  'outer_scalar_lifetime_recreated':{'StorageLive':11},
 }.items():
  changed=copy.deepcopy(ll);f=next(f for f in changed['fun_decls']if f and f['def_id']==320);loop=find(f['body'],23084)['kind']['Loop'];loop['statements'].insert(0,dict(id=-1,kind=kind));rs,_=scan(changed,g)
  assert not any(r['function_id']==320 and r['statement']==30584 for r in rs);controls[label]='no inherited bound emitted'
 name='PV_B3P_NestedIndices587227';s='import PV_B3P_RangeEvents578227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n'
 for j,r in enumerate(rows):
  r['lemma']=name+f'.certificate_{j}';n,slack=r['limit'],r['slack']
  if r['route']=='range':ns='PV_B3P_RangeEvents578227';params='(handler : Str → Result Never) (start : Usize)';args=f'handler ⟨start,{n}#usize⟩ {slack} effects'
  else:ns='PV_B3P_DominatedEvents578227';params='(index : Nat)';args=f'{n} {slack} index effects'
  s+=f'''/-- Checked nested frame: source event {r['instance']}:{r['statement']}. -/
def sourceState_{j} {params} (effects : List (Result Unit)) : Result (Option IndexState) :=
  {ns}.sourceEvent {args}
theorem certificate_{j} {{α : Type}} {params} (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_{j} {('handler start'if r['route']=='range'else'index')} effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  {ns}.event_certificate {args} observed ran normal first second
#print axioms certificate_{j}
'''
 outputs={D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'NESTED-INDICES-D587.json':json.dumps(dict(rows=rows,count=len(rows),chunks=[name],source_frames=sources,llbc_sha256=sha(raw),negative_controls=controls,validation_status='PREPARATION; focused Lean compiles and raw NEP audit pending',evidence_class='SCRIPT-CHECKED own-1 scalar nested-loop stack frame plus named kernel event guards',whole_caller_association=False,native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',borrow_restoration=False,premises_removed=[]),indent=2)+'\n'}
 for p,s in outputs.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=len(rows),controls=controls,check=a.check)))
if __name__=='__main__':main()
