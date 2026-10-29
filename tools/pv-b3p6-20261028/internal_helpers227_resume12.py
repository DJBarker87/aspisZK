"""Bind each internal-layer helper to its four ordered source limb actions."""
from pathlib import Path
import sys,json
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';files={}
h='namespace PV_B3P_Binding12227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result\nset_option autoImplicit false\n'
pre='import PV_B3P_InternalSteps12227\nimport PV_B3P_PreweightedMacro12227\n'
s=pre+h+'''
def internal_limb12 (limbs : Array U32 4#usize) (sum : InternalSum12) (index : Usize) : Result InternalSum12 := do
  let value ← Array.index_usize limbs index
  let wide ← lift (core.convert.num.FromU64U32.from value)
  let old ← Array.index_usize sum index
  let next ← lift (U64.wrapping_add old wide)
  Array.update sum index next
def source_internal_sum12 (sum : InternalSum12) (value : aspis_core.field.QM31) : Result InternalSum12 := do
  let limbs ← reference_poseidon.extension_limbs value
  loop (usize_body (internal_limb12 limbs) 4#usize) (sum,0#usize)
attribute [local irreducible] Array.index_usize Array.update U64.wrapping_add reference_poseidon.extension_limbs
theorem internal_sum_helper_binding12 (sum : InternalSum12) (value : aspis_core.field.QM31) :
    reference_poseidon.internal_sum227 sum value = source_internal_sum12 sum value := by
  unfold reference_poseidon.internal_sum227 source_internal_sum12
  apply bind_equal9
  intro limbs
  rw [usize_loop_plan (internal_limb12 limbs) 4#usize 0#usize 4 sum (by scalar_tac)]
  have h01 : Usize.wrapping_add 0#usize 1#usize = 1#usize := next_exact _ _ rfl
  have h12 : Usize.wrapping_add 1#usize 1#usize = 2#usize := next_exact _ _ rfl
  have h23 : Usize.wrapping_add 2#usize 1#usize = 3#usize := next_exact _ _ rfl
  simp only [usize_plan,internal_limb12,h01,h12,h23,lift,bind_tc_ok,
    PV_B3P_Ordered227.bind_assoc,bind_return12]
#print axioms internal_sum_helper_binding12
end PV_B3P_Binding12227
''';files['PV_B3P_InternalLimb12227']=s
s=pre+h+'''
def internal_full_read12 (sum : InternalSum12) (old : Array U32 4#usize) (limb : Usize) : Result U64 := do
  let a ← Array.index_usize sum limb
  let b ← Array.index_usize old limb
  let wide ← lift (core.convert.num.FromU64U32.from b)
  lift (U64.wrapping_add a wide)
attribute [local irreducible] Array.index_usize U64.wrapping_add
theorem internal_full_helper_binding12 (sum : InternalSum12) (old : Array U32 4#usize) :
    reference_poseidon.internal_full_sum227 sum old = four_build12 (internal_full_read12 sum old) := by
  simp only [reference_poseidon.internal_full_sum227,four_build12,internal_full_read12,
    lift,bind_tc_ok,PV_B3P_Ordered227.bind_assoc]
#print axioms internal_full_helper_binding12
end PV_B3P_Binding12227
''';files['PV_B3P_InternalFull12227']=s
s=pre+h+'''
def internal_zero_read12 (sum : InternalSum12) (old : Array U32 4#usize) (limb : Usize) : Result U64 := do
  let a ← Array.index_usize sum limb
  let p ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let added ← lift (U64.wrapping_add a p)
  let b ← Array.index_usize old limb
  let wide ← lift (core.convert.num.FromU64U32.from b)
  lift (U64.wrapping_sub added wide)
attribute [local irreducible] Array.index_usize U64.wrapping_add U64.wrapping_sub reference_poseidon.extension_from_raw_limbs
theorem internal_zero_helper_binding12 (sum : InternalSum12) (old : Array U32 4#usize) :
    reference_poseidon.internal_zero227 sum old = (do
      let raw ← four_build12 (internal_zero_read12 sum old)
      reference_poseidon.extension_from_raw_limbs raw) := by
  simp only [reference_poseidon.internal_zero227,four_build12,internal_zero_read12,
    lift,bind_tc_ok,PV_B3P_Ordered227.bind_assoc]
#print axioms internal_zero_helper_binding12
end PV_B3P_Binding12227
''';files['PV_B3P_InternalZero12227']=s
s=pre+h+'''
def internal_shift_read12 (sum : InternalSum12) (limbs : Array U32 4#usize) (shift : U8) (limb : Usize) : Result U64 := do
  let a ← Array.index_usize sum limb
  let b ← Array.index_usize limbs limb
  let wide ← lift (core.convert.num.FromU64U32.from b)
  let shifted ← lift (U64.wrapping_shl wide (UScalar.cast .U32 shift))
  lift (U64.wrapping_add a shifted)
attribute [local irreducible] Array.index_usize U64.wrapping_add U64.wrapping_shl reference_poseidon.extension_limbs reference_poseidon.extension_from_raw_limbs
theorem internal_shift_helper_binding12 (value : aspis_core.field.QM31) (sum : InternalSum12) (shift : U8) :
    reference_poseidon.internal_shift227 value sum shift = (do
      let limbs ← reference_poseidon.extension_limbs value
      let raw ← four_build12 (internal_shift_read12 sum limbs shift)
      reference_poseidon.extension_from_raw_limbs raw) := by
  simp only [reference_poseidon.internal_shift227,four_build12,internal_shift_read12,
    lift,bind_tc_ok,PV_B3P_Ordered227.bind_assoc]
#print axioms internal_shift_helper_binding12
end PV_B3P_Binding12227
''';files['PV_B3P_InternalShift12227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
if '--check'not in sys.argv:(D/'resume12/internal-helper-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')
