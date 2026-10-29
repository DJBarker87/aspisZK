import PV_B3P_InternalSteps12227
import PV_B3P_PreweightedMacro12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false

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
