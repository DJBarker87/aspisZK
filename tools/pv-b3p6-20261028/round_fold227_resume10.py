"""Named ordered flattening, then four actual full-round applications."""
from pathlib import Path
import json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume10';files={}
header='''namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
'''
groups=['['+', '.join(f'{i}#usize'for i in range(n,n+4))+']'for n in [0,4,8,12]];allidx='['+', '.join(f'{i}#usize'for i in range(16))+']'
s='import PV_B3P_Ordered227\nimport PV_B3P_DigestCpsEq9227\n'+header
s+='''
theorem sixteen_group_finish10 {α β : Type} (step : α → Usize → Result α)
    (initial : α) (finish : α → Result β) :
    (do
'''
prev='initial'
for i,g in enumerate(groups):s+=f'      let s{i} ← PV_B3P_Ordered227.fold step {g} {prev}\n';prev=f's{i}'
s+=f'''      finish s3) = (do
      let next ← PV_B3P_Ordered227.fold step {allidx} initial
      finish next) := by
  have h := PV_B3P_Ordered227.flatten step ['''+', '.join(groups)+'''] initial
  have joined := congrArg (fun result => result >>= finish) h
  simpa only [PV_B3P_Ordered227.ranges,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using joined
#print axioms sixteen_group_finish10
end PV_B3P_Binding10227
''';files['PV_B3P_SixteenGroups10227']=s
s='import PV_B3P_RoundQPlain10227\nimport PV_B3P_RoundQPacked10227\nimport PV_B3P_RoundMPlain10227\nimport PV_B3P_RoundMPacked10227\n'+header
s+='\nattribute [local irreducible] round_q_step10 round_m_step10 reference_poseidon.external_linear_lazy reference_poseidon.external_linear_packed\n'
rows=[]
for kind in ['q','m']:
 for packed in [False,True]:
  name=('full_round'if kind=='q'else'full_round_m31_constants')+('_packed'if packed else'');ctype='aspis_core.field.QM31'if kind=='q'else'U32';finish='reference_poseidon.external_linear_packed'if packed else'reference_poseidon.external_linear_lazy'
  s+=f'''\ntheorem {name}_source_fold10 (state : RoundState10) (constants1 : Array {ctype} 16#usize) :
    reference_poseidon.{name} state constants1 = (do
      let next ← PV_B3P_Ordered227.fold (round_{kind}_step10 constants1) {allidx} state
      {finish} next) := by
  rw [{name}_body_binding10]
  unfold round_{kind}_group10_00 round_{kind}_folded10_04 round_{kind}_folded10_08 round_{kind}_folded10_12
    round_{kind}_group10_04 round_{kind}_group10_08 round_{kind}_group10_12
  have h := PV_B3P_Ordered227.flatten (round_{kind}_step10 constants1) [{', '.join(groups)}] state
  have joined := congrArg (fun result => result >>= {finish}) h
  simpa only [PV_B3P_Ordered227.ranges,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using joined
#print axioms {name}_source_fold10
''';rows.append(dict(body=name,theorem=name+'_source_fold10',iterations=16))
s+='end PV_B3P_Binding10227\n';files['PV_B3P_RoundSourceFold10227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
record=dict(modules=list(files),applications=rows,credit='four complete emitted round bodies to exact ordered16-lane source plan; source loop token checks separate and caller/std bindings retained',semantic_use='reclassification within existing Charon/Aeneas tool trust')
p=O/'round-source-fold-bindings.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
