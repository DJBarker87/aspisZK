"""Arithmetic scalar observations of actual Range next outputs.
Range-derived bounds remain labelled and consume the actual next in generated events.
"""
from pathlib import Path
import argparse,json,lzma,copy,hashlib
from source_normalize583 import constants,normalize
from range_indices578 import seeds
from initializer_source578 import find
from frame_indices578 import dicts
from specialized_indices578 import instantiate
from arithmetic_range_collect592 import collect
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031'
sha=lambda b:hashlib.sha256(b).hexdigest()
def render(e,inputs):
 op=e['op']
 if op=='literal':return f"(.literal {e['value']})"
 if op=='bounded':
  assert e['input'][0]=='rangeItem';key=e['input'][1]
  if key not in inputs:inputs.append(key)
  return f"(.bounded item.val {e['limit']})"
 if op in ['add','mul']:return f"(.{op} {render(e['left'],inputs)} {render(e['right'],inputs)} (UScalar.size .Usize))"
 raise AssertionError(e)
def scan(ll,g):
 fs={f['def_id']:f for f in ll['fun_decls']if f};vs,_=constants(ll,fs);rows=[];frames=[]
 remaining={(r['instance'],r['statement'])for group in json.loads((R/'SOURCE-COVERAGE-D587.json').read_text())['groups'].values()for r in group['remaining']}
 for inst,v in g['instances'].items():
  original=fs[v['id']].get('body')
  if not isinstance(original,dict):continue
  subst=[];b=instantiate(original,v['environment']['const_generics'],subst)if v['environment']['const_generics']else original;b,changes=normalize(b,vs);sd,ff=seeds(b);new=[]
  for r in collect(b,sd):
   if(inst,r['statement'])not in remaining:continue
   inputs=[];expr=render(r['expression'],inputs)
   assert len(inputs)==1
   seed=next(q for q in sd.values()if q[2]==inputs[0]);r.update(instance=inst,function_id=v['id'],range_next=inputs[0],range_limit=seed[1],expression_lean=expr);rows.append(r);new.append(r['statement'])
  if new:frames.append(dict(instance=inst,original_sha256=sha(json.dumps(original,sort_keys=True).encode()),normalizations=changes,range_frames=ff,statements=new))
 return rows,frames

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];g=json.loads((I/'direct3-instantiated-callcone.json').read_text());rows,frames=scan(ll,g);assert len(rows)==6
 controls={}
 for fid,sid,label in [(232,17931,'range_offset_changed'),(239,18736,'occupancy_offset_changed')]:
  # Every changed arithmetic projection must either lose its bound or change
  # its emitted expression; it must never silently retain the old certificate.
  changed=copy.deepcopy(ll);f=next(f for f in changed['fun_decls']if f and f['def_id']==fid)
  # Select an actual offset add from a certified event's source data by snapshot.
  rr=next(r for r in rows if r['function_id']==fid);snap=rr['index_snapshot'];actual=find(f['body'],snap[1]);old=copy.deepcopy(actual);actual['kind']={'StorageDead':999}
  rs,_=scan(changed,g);assert not any(r['instance']==rr['instance']and r['statement']==rr['statement']for r in rs);controls[label]=dict(statement=old['id'],result='no guard emitted')
 name='PV_B3P_RangeArithmetic592227';s='import PV_B3P_RangeComputedEvents592227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n'
 for j,r in enumerate(rows):
  r['lemma']=name+f'.certificate_{j}';expr=r['expression_lean'];args=f'handler ⟨start,{r["range_limit"]}#usize⟩ (fun item => {expr}) {r["slack"]} effects'
  s+=f'''/-- Actual source Range next {r['range_next']} then scalar event {r['instance']}:{r['statement']}. -/
def sourceState_{j} (handler : Str → Result Never) (start : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_RangeComputedEvents592227.sourceEvent {args}
theorem certificate_{j} {{α : Type}} (handler : Str → Result Never) (start : Usize)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceState_{j} handler start effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_RangeComputedEvents592227.event_certificate {args} observed ran normal first second
#print axioms certificate_{j}
'''
 data=dict(rows=rows,count=len(rows),chunks=[name],source_frames=frames,llbc_sha256=sha(raw),negative_controls=controls,evidence_class='SCRIPT-CHECKED own-1 Range next and arithmetic scalar projections plus named kernel guards',validation_status='PREPARATION; compile and raw NEP audit required',native_pointer_validity='consumes pv-evhB4 shared owner relation when supplied',whole_caller_association=False,premises_removed=[])
 for p,t in {D/'lean'/(name+'.lean'):s+'end '+name+'\n',R/'RANGE-ARITHMETIC-D592.json':json.dumps(data,indent=2)+'\n'}.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(count=len(rows),controls=controls,check=a.check)))
if __name__=='__main__':main()
