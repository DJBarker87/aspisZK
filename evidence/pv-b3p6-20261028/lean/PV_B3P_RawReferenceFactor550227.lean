import PV_B3P_RawRefTail0550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227
set_option autoImplicit false
attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from

theorem raw_reference_factor550 (input : Array aspis_core.field.QM31 4#usize) :
    reference_poseidon.external_local_packed_raw input = (do
  let q ← Array.index_usize input 0#usize
  let a ← reference_poseidon.extension_limbs q
  let q1 ← Array.index_usize input 1#usize
  let a1 ← reference_poseidon.extension_limbs q1
  let q2 ← Array.index_usize input 2#usize
  let a2 ← reference_poseidon.extension_limbs q2
  let q3 ← Array.index_usize input 3#usize
  let a3 ← reference_poseidon.extension_limbs q3
  raw_reference_tail0_550 a a1 a2 a3) := by
  unfold reference_poseidon.external_local_packed_raw
  apply bind_equal9
  intro q
  apply bind_equal9
  intro a
  apply bind_equal9
  intro q1
  apply bind_equal9
  intro a1
  apply bind_equal9
  intro q2
  apply bind_equal9
  intro a2
  apply bind_equal9
  intro q3
  apply bind_equal9
  intro a3
  exact raw_reference_tail0_factor550 a a1 a2 a3

#print axioms raw_reference_factor550
end PV_B3P_Association550227
