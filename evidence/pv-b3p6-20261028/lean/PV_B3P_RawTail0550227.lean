import PV_B3P_RawTail1550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from

theorem raw_tail0_binding550 (a4 a6 a7 a8 : Limbs32_550) :
    raw_native_tail0_550 a4 a6 a7 a8  =
      raw_reference_tail0_550 a4 a6 a7 a8  := by
  unfold raw_native_tail0_550 raw_reference_tail0_550
  rw [raw_row_continuation550]
  simp only [four_index_zero550,four_index_one550,four_index_two550,four_index_three550,bind_tc_ok]
  simp only [raw_tail1_binding550]
  rfl

#print axioms raw_tail0_binding550
end PV_B3P_Association550227
