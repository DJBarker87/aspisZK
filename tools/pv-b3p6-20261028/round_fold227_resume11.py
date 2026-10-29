"""Repair 64096 by a tiny named list partition and explicit Result transport."""
from pathlib import Path
import sys
L=Path('evidence/pv-b3p6-20261028/lean'); files={}
groups=['['+', '.join(f'{i}#usize' for i in range(n,n+4))+']' for n in [0,4,8,12]];g='['+', '.join(groups)+']';allidx='['+', '.join(f'{i}#usize' for i in range(16))+']'
h='namespace PV_B3P_Binding11227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227\nset_option autoImplicit false\n'
s='import PV_B3P_Ordered227\nimport PV_B3P_DigestCpsEq9227\n'+h
s+=f'theorem usize_partition11 : ({g} : List (List Usize)).flatten = {allidx} := by\n  rfl\n#print axioms usize_partition11\nend PV_B3P_Binding11227\n';files['PV_B3P_UsizePartition11227']=s
s='import PV_B3P_UsizePartition11227\n'+h
s+='theorem sixteen_finish11 {α β : Type} (step : α → Usize → Result α) (initial : α) (finish : α → Result β) :\n    (do\n'
for i,v in enumerate(groups):s+=f'      let s{i} ← PV_B3P_Ordered227.fold step {v} '+('initial' if i==0 else f's{i-1}')+'\n'
s+=f'''      finish s3) = (PV_B3P_Ordered227.fold step {allidx} initial >>= finish) := by
  have h := PV_B3P_Ordered227.flatten step {g} initial
  rw [usize_partition11] at h
  have joined := congrArg (fun result => result >>= finish) h
  simpa only [PV_B3P_Ordered227.ranges, PV_B3P_Ordered227.bind_assoc, bind_tc_ok] using joined
#print axioms sixteen_finish11
end PV_B3P_Binding11227
''';files['PV_B3P_SixteenFinish11227']=s
for kind in ['q','m']:
 for packed in [False,True]:
  name=('full_round' if kind=='q' else 'full_round_m31_constants')+('_packed'if packed else'');mod='PV_B3P_Round'+kind.upper()+('Packed'if packed else'Plain')+'11227';old='PV_B3P_Round'+kind.upper()+('Packed'if packed else'Plain')+'10227';ctype='aspis_core.field.QM31' if kind=='q' else'U32';finish='reference_poseidon.external_linear_'+('packed'if packed else'lazy')
  s=f'import {old}\nimport PV_B3P_SixteenFinish11227\n'+h+'open PV_B3P_Binding10227\n'
  s+=f'attribute [local irreducible] round_{kind}_step10 {finish}\n'
  s+=f'''theorem {name}_source_fold11 (state : RoundState10) (constants1 : Array {ctype} 16#usize) :
    reference_poseidon.{name} state constants1 = (PV_B3P_Ordered227.fold (round_{kind}_step10 constants1) {allidx} state >>= {finish}) := by
  rw [{name}_body_binding10]
  unfold round_{kind}_group10_00 round_{kind}_folded10_04 round_{kind}_folded10_08 round_{kind}_folded10_12 round_{kind}_group10_04 round_{kind}_group10_08 round_{kind}_group10_12
  exact sixteen_finish11 (round_{kind}_step10 constants1) state {finish}
#print axioms {name}_source_fold11
end PV_B3P_Binding11227
''';files[mod]=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
