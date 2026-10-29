import PV_B3P_InternalSteps12227
import PV_B3P_PreweightedMacro12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false

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
