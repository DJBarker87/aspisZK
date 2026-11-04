"""Retain typed private usize observations through immutable shared borrows.
Only source-language scalar identity is bound; native ownership stays separate.
"""
from pathlib import Path
import argparse,json,lzma,hashlib,copy
from source_normalize583 import constants,normalize
from specialized_indices578 import instantiate
from range_caps587 import seeds
from shared_scalar_collect587 import collect
from frame_indices578 import dicts
from initializer_source578 import find
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def scan(ll,g):
 definitions=[x['HashConsedValue'][1]for x in dicts(ll)if isinstance(x.get('HashConsedValue'),list)and x['HashConsedValue'][0]==1112];assert definitions and all(t=={'Literal':{'UInt':'Usize'}}for t in definitions)
 fs={f['def_id']:f for f in ll['fun_decls']if f};vs,_=constants(ll,fs);rem={(r['instance'],r['statement'])for v in json.loads((R/'SOURCE-COVERAGE-D584.json').read_text())['groups'].values()for r in v['remaining']};rem-={(r['instance'],r['statement'])for r in json.loads((R/'NESTED-INDICES-D587.json').read_text())['rows']};rows=[];frames=[]
 for inst,v in g['instances'].items():
  if v['id']not in[218,362]:continue
  original=fs[v['id']]['body'];b=instantiate(original,v['environment']['const_generics'],[])if v['environment']['const_generics']else original;b,nn=normalize(b,vs);sd,ff=seeds(b);rs,nested=collect(b,sd);accepted=[]
  for r in rs:
   if(inst,r['statement'])not in rem:continue
   rem.remove((inst,r['statement']));rows.append(dict(instance=inst,function_id=v['id'],route='range'if r['predicate_statement']in{v[2]for v in sd.values()}else'flow',**r));accepted.append(r['statement'])
  if accepted:frames.append(dict(instance=inst,source_sha256=sha(json.dumps(original,sort_keys=True).encode()),normalizations=nn,range_frames=ff,nested_frames=nested,statements=accepted))
 return rows,frames

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];g=json.loads((I/'direct3-instantiated-callcone.json').read_text());rows,frames=scan(ll,g);assert len(rows)==2;controls={}
 for label,edit in [('mutable_scalar_borrow',lambda r:r.__setitem__('kind','Mut')),('raw_scalar_address',None)]:
  changed=copy.deepcopy(ll);f=next(f for f in changed['fun_decls']if f and f['def_id']==362);rhs=find(f['body'],24519)['kind']['Assign'][1]
  if edit:edit(rhs['Ref'])
  else:rhs['RawPtr']=rhs.pop('Ref')
  rs,_=scan(changed,g);assert not any(r['statement']==30806 for r in rs);controls[label]='no immutable scalar frame emitted'
 name='PV_B3P_SharedScalarIndices587227';s='import PV_B3P_RangeEvents578227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n'
 for j,r in enumerate(rows):
  r['lemma']=name+f'.certificate_{j}';n,slack=r['limit'],r['slack'];ns='PV_B3P_RangeEvents578227'if r['route']=='range'else'PV_B3P_DominatedEvents578227';params='(handler : Str → Result Never) (start : Usize)'if r['route']=='range'else'(index : Nat)';args=f'handler ⟨start,{n}#usize⟩ {slack} effects'if r['route']=='range'else f'{n} {slack} index effects';params2='handler start'if r['route']=='range'else'index'
  s+=f'''/-- Actual typed shared scalar frame at {r['instance']}:{r['statement']}. -/
def sourceState_{j} {params} (effects : List (Result Unit)) : Result (Option IndexState) :=
  {ns}.sourceEvent {args}
theorem certificate_{j} {{α : Type}} {params} (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_{j} {params2} effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  {ns}.event_certificate {args} observed ran normal first second
#print axioms certificate_{j}
'''
 x=dict(rows=rows,count=2,chunks=[name],source_frames=frames,llbc_sha256=sha(raw),negative_controls=controls,validation_status='PREPARATION; focused Lean compiles and raw NEP audit pending',evidence_class='SCRIPT-CHECKED own-1 typed immutable source usize borrow scalar projection plus named kernel guards',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',whole_caller_association=False,native_borrow_restoration=False,premises_removed=[])
 for p,s in{D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'SHARED-SCALAR-INDICES-D587.json':json.dumps(x,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==s,p
  else:p.write_text(s)
 print(json.dumps(dict(new_indices=2,check=a.check,controls=controls)))
if __name__=='__main__':main()
