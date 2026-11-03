"""Source-state mapping for guarded wrapping subtraction windows."""
from pathlib import Path
import argparse,copy,hashlib,json,lzma
from initializer_source578 import find
from frame_indices578 import dicts
from dominated_indices578 import collect
from specialized_indices578 import instantiate
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031';sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};g=json.loads((I/'direct3-instantiated-callcone.json').read_text());prior=json.loads((R/'SOURCE-COVERAGE-D572.json').read_text());already={(r['instance'],r['statement'])for v in prior['groups'].values()for r in v['certified']}
 for n in ['INITIALIZER-SOURCE','FRAME-INDICES','SLICE-SOURCE','DOMINATED-INDICES','SPECIALIZED-INDICES','RANGE-INDICES']:already.update((r['instance'],r['statement'])for r in json.loads((R/(n+'-D578.json')).read_text())['rows'])
 rows=[];fixture=None
 for inst,v in g['instances'].items():
  f=fs[v['id']];body=f.get('body')
  if not body:continue
  subst=[];body=instantiate(body,v['environment']['const_generics'],subst)if v['environment']['const_generics']else body
  for row in collect(body,windows=True):
   if row.get('kind')!='window'or(inst,row['statement'])in already:continue
   if fixture is None:fixture=(copy.deepcopy(body),row)
   rows.append(dict(instance=inst,environment=v['environment'],body_sha256=sha(json.dumps(f['body'],sort_keys=True).encode()),substitutions=subst,**row));already.add((inst,row['statement']))
 controls={};body,row=fixture;target=row['statement'];lower=row['lower_test'][0];upper=row['upper_test'][0]
 sub=next(x for x in dicts(body)if isinstance(x.get('kind'),dict)and 'Assign'in x['kind']and x['kind']['Assign'][0]['kind']=={'Local':row['source_call']['kind']['Call']['call']['args'][-1]['Copy']['kind']['Local']}and x['kind']['Assign'][1].get('BinaryOp',[None])[0]=={'Sub':'Wrap'})
 subid=sub['id']
 edits={
  'missing_lower_guard':lambda b:find(b,lower)['kind']['Assign'][1]['BinaryOp'].__setitem__(0,'Eq'),
  'nonstrict_upper_guard':lambda b:find(b,upper)['kind']['Assign'][1]['BinaryOp'].__setitem__(0,'Le'),
  'wrong_arithmetic':lambda b:find(b,subid)['kind']['Assign'][1]['BinaryOp'].__setitem__(0,{'Add':'Wrap'}),
  'wrong_base':lambda b:find(b,subid)['kind']['Assign'][1]['BinaryOp'].__setitem__(2,{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','0']}}}}}),
 }
 for label,edit in edits.items():
  changed=copy.deepcopy(body);edit(changed)
  assert not any(x['statement']==target and x.get('kind')=='window'for x in collect(changed,windows=True)),label
  controls[label]='no window certificate emitted'
 outputs={};chunks=[]
 for offset in range(0,len(rows),24):
  name=f'PV_B3P_WindowIndices578227_{offset//24:02d}';chunks.append(name)
  s='import PV_B3P_WindowEvents578227\nnamespace '+name+'\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_WindowEvents578227\nset_option autoImplicit false\n'
  for j,row in enumerate(rows[offset:offset+24],offset):
   row['lemma']=name+f'.certificate_{j}';limit,slack=row['limit'],row['slack']
   s+=f'''/-- Actual source instance {row['instance']}, instruction {row['statement']}. -/
def sourceState_{j} (base value : Usize) (effects : List (Result Unit)) : Result (Option IndexState) :=
  sourceEvent base {limit}#usize value {slack} effects
theorem certificate_{j} {{α : Type}} (base value : Usize) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceState_{j} base value effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_certificate base {limit}#usize value {slack} effects observed ran normal first second
#print axioms certificate_{j}
'''
  s+='end '+name+'\n';outputs[D/'lean'/(name+'.lean')]=s
 meta=dict(llbc_sha256=sha(raw),rows=rows,count=len(rows),chunks=chunks,negative_controls=controls,evidence_class='script-checked own-1 two-comparison scalar window projection plus Lean wrapping arithmetic event guard',native_pointer_validity=False,whole_caller_association=False,premises_removed=[])
 outputs[R/'WINDOW-INDICES-D578.json']=json.dumps(meta,indent=2)+'\n'
 for p,t in outputs.items():
  if a.check:assert p.read_text()==t,p
  else:p.write_text(t)
 print(json.dumps(dict(new_indices=len(rows),chunks=chunks,check=a.check)))
if __name__=='__main__':main()
