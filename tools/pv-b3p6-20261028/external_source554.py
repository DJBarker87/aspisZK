"""Source group interpreter; every local raw row remains symbolic."""
from pathlib import Path
import sys
L=Path('evidence/pv-b3p6-20261028/lean')
def emit(p,s):
 if '--check' in sys.argv:assert p.read_text()==s,str(p)
 else:p.write_text(s)
head='''namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227 PV_B3P_Association550227
set_option autoImplicit false
'''
s='import PV_B3P_RawSource550227\nimport PV_B3P_P227_03a\nimport Lean.Elab.Tactic.AsAuxLemma\n'+head+'''
def external_group_source554 (input : Array aspis_core.field.QM31 4#usize) :
    Result (Array aspis_core.field.QM31 4#usize) := do
  let limbs ← raw_input550 input
  let a ← Array.index_usize limbs 0#usize
  let b ← Array.index_usize limbs 1#usize
  let c ← Array.index_usize limbs 2#usize
  let d ← Array.index_usize limbs 3#usize
'''
for j in range(4):s+=f'  let r{j} ← raw_row550 a b c d {j}#usize\n  let q{j} ← reference_poseidon.extension_from_raw_limbs r{j}\n'
s+='  .ok (Array.make 4#usize [q0,q1,q2,q3] (by simp only [List.length_cons,List.length_nil]; rfl))\n'
s+='''
attribute [local irreducible] Aeneas.Std.bind Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 reference_poseidon.extension_from_raw_limbs
  U64.wrapping_add U64.wrapping_sub U64.wrapping_mul core.convert.num.FromU64U32.from

theorem external_group_reference554 (input : Array aspis_core.field.QM31 4#usize) :
    external_group_source554 input = reference_poseidon.external_group227 input := by
  unfold external_group_source554 reference_poseidon.external_group227
  rw [raw_input_continuation550]
  simp only [four_index_zero550,four_index_one550,four_index_two550,four_index_three550,bind_tc_ok]
'''
indent='  '
for n in range(8):s+=indent+'apply bind_equal9\n'+indent+f'intro input{n}\n'
for j in range(4):
 s+=indent+'as_aux_lemma =>\n';indent+='  '
 s+=indent+'rw [raw_row_continuation550]\n'
 for k in range(36):
  if k==18:s+=indent+'as_aux_lemma =>\n';indent+='  '
  s+=indent+'apply bind_equal9\n'+indent+f'intro row{j}cell{k}\n'
 s+=indent+'apply bind_equal9\n'+indent+f'intro output{j}\n'
s+=indent+'rfl\n\n#print axioms external_group_reference554\nend PV_B3P_Association554227\n'
emit(L/'PV_B3P_ExternalGroup554227.lean',s)
print('four symbolic raw rows and all four reconstructions emitted')
