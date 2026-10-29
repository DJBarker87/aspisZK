import PV_B3P_InternalSteps12227
import PV_B3P_PreweightedMacro12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false

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
