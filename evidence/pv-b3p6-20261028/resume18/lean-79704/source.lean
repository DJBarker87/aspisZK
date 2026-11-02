import PV_B3P_RawRowContinuation550227
import PV_B3P_P227_02
namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227 PV_B3P_Association550227
set_option autoImplicit false

def external_add_source554 (value : aspis_core.field.QM31) (sums : Limbs64_550) :
    Result aspis_core.field.QM31 := do
  let limbs ← reference_poseidon.extension_limbs value
  let raw ← from_fn_four550 (fun limb => do
    let v ← Array.index_usize limbs limb
    let wide ← lift (core.convert.num.FromU64U32.from v)
    let sum ← Array.index_usize sums limb
    lift (U64.wrapping_add wide sum))
  reference_poseidon.extension_from_raw_limbs raw

attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.extension_from_raw_limbs U64.wrapping_add core.convert.num.FromU64U32.from

theorem external_add_reference554 (value : aspis_core.field.QM31) (sums : Limbs64_550) :
    external_add_source554 value sums = reference_poseidon.add_global227 value sums := by
  simp only [external_add_source554,from_fn_four550,reference_poseidon.add_global227,
    PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms external_add_reference554
end PV_B3P_Association554227
