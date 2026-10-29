import PV_B3P_InternalSteps12227
import PV_B3P_PreweightedMacro12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false

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
