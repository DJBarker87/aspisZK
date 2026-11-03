"""Resolve actual const-generic environments before existing frame passes.
No new analysis rule: exact Free const substitutions from the captured graph.
"""
from pathlib import Path
import argparse,hashlib,json,lzma
from fixed_indices572 import literal
from frame_indices578 import collect as fixed
from dominated_indices578 import collect as dominated
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def instantiate(x,constants,log,path=()):
 if isinstance(x,dict):
  if 'ty'in x and x.get('kind',{}).get('Var',{}).get('Free')is not None:
   idx=x['kind']['Var']['Free'];assert idx<len(constants),(idx,constants)
   assert literal(constants[idx])is not None,constants[idx]
   log.append(dict(path=list(path),parameter=idx,argument=constants[idx]))
   return dict(x,kind=constants[idx]['kind'])
  return {k:instantiate(v,constants,log,path+(k,))for k,v in x.items()}
 if isinstance(x,list):return[instantiate(v,constants,log,path+(j,))for j,v in enumerate(x)]
 return x

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());prior=json.loads((R/'SOURCE-COVERAGE-D572.json').read_text());already={(r['instance'],r['statement'])for v in prior['groups'].values()for r in v['certified']}
 for n in ['INITIALIZER-SOURCE-D578.json','FRAME-INDICES-D578.json','SLICE-SOURCE-D578.json','DOMINATED-INDICES-D578.json']:already.update((r['instance'],r['statement'])for r in json.loads((R/n).read_text())['rows'])
 rows=[];bindings=[]
 for inst,v in g['instances'].items():
  cs=v['environment']['const_generics'];body=fs[v['id']].get('body')
  if not cs or not body:continue
  substitutions=[];specialized=instantiate(body,cs,substitutions);bindings.append(dict(instance=inst,const_arguments=cs,source_body_sha256=sha(json.dumps(body,sort_keys=True).encode()),specialized_body_sha256=sha(json.dumps(specialized,sort_keys=True).encode()),substitutions=substitutions))
  for kind,found in [('fixed',fixed(specialized)[0]),('dominated',dominated(specialized))]:
   for row in found:
    key=inst,row['statement']
    if key in already:continue
    already.add(key);rows.append(dict(instance=inst,environment=v['environment'],kind=kind,**row))
 outputs={};chunks=[]
 for offset in range(0,len(rows),24):
  name=f'PV_B3P_SpecializedIndices578227_{offset//24:02d}';chunks.append(name)
  s='import PV_B3P_FixedIndex572227\nimport PV_B3P_DominatedEvents578227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n'
  for j,row in enumerate(rows[offset:offset+24],offset):
   row['lemma']=name+f'.certificate_{j}';s+=f"/-- Exact const specialization {row['instance']}, source instruction {row['statement']}. -/\n"
   if row['kind']=='fixed':
    s+=f'''def sourceState_{j} : IndexState := ⟨{row['index']},{row['length']}⟩
theorem certificate_{j} {{α : Type}} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_{j}) ∧
      branch (indexGuard sourceState_{j}) normal first = branch (indexGuard sourceState_{j}) normal second :=
  PV_B3P_FixedIndex572227.fixed_certificate {row['index']} {row['spare']} normal first second
'''
   else:
    s+=f'''def sourceState_{j} (index : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  PV_B3P_DominatedEvents578227.sourceEvent {row['limit']} {row['slack']} index effects
theorem certificate_{j} {{α : Type}} (index : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_{j} index effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  PV_B3P_DominatedEvents578227.event_certificate {row['limit']} {row['slack']} index effects observed ran normal first second
'''
   s+=f'#print axioms certificate_{j}\n'
  s+='end '+name+'\n';outputs[D/'lean'/(name+'.lean')]=s
 meta=dict(llbc_sha256=sha(raw),rows=rows,count=len(rows),chunks=chunks,specializations=bindings,evidence_class='exact captured const-generic substitution followed by unchanged private scalar constant/dominance passes',pointer_validity=False,whole_caller_association=False,premises_removed=[])
 outputs[R/'SPECIALIZED-INDICES-D578.json']=json.dumps(meta,indent=2)+'\n'
 for p,t in outputs.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(new_indices=len(rows),chunks=chunks,check=a.check)))
if __name__=='__main__':main()
