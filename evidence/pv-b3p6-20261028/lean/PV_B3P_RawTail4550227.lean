import PV_B3P_RawTails550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from

theorem raw_tail4_binding550  (i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 i64 i69 i74 i79 : U64) :
    raw_native_tail4_550 (Array.make 4#usize [i4,i9,i14,i19] (by simp only [List.length_cons,List.length_nil]; rfl)) (Array.make 4#usize [i24,i29,i34,i39] (by simp only [List.length_cons,List.length_nil]; rfl)) (Array.make 4#usize [i44,i49,i54,i59] (by simp only [List.length_cons,List.length_nil]; rfl)) (Array.make 4#usize [i64,i69,i74,i79] (by simp only [List.length_cons,List.length_nil]; rfl)) =
      raw_reference_tail4_550 i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 i64 i69 i74 i79 := by
  unfold raw_native_tail4_550 raw_reference_tail4_550
  simp only [ignored_source_debug_loops550]
  exact (raw_suffix550 i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 i64 i69 i74 i79).symm

#print axioms raw_tail4_binding550
end PV_B3P_Association550227
