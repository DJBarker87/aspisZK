import PV_B3P_RawTail4550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from

theorem raw_tail3_binding550 (a4 a6 a7 a8 : Limbs32_550) (i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 : U64) :
    raw_native_tail3_550 a4 a6 a7 a8 (Array.make 4#usize [i4,i9,i14,i19] (by simp only [List.length_cons,List.length_nil]; rfl)) (Array.make 4#usize [i24,i29,i34,i39] (by simp only [List.length_cons,List.length_nil]; rfl)) (Array.make 4#usize [i44,i49,i54,i59] (by simp only [List.length_cons,List.length_nil]; rfl)) =
      raw_reference_tail3_550 a4 a6 a7 a8 i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 := by
  unfold raw_native_tail3_550 raw_reference_tail3_550
  rw [raw_row_continuation550]
  simp only [raw_tail4_binding550]
  rfl

#print axioms raw_tail3_binding550
end PV_B3P_Association550227
