import R1Z.PV_Src_ExternalBlocks

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalSums
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderPoseidonReference

theorem total (state : Array U32 16#usize) (sums : Array U64 4#usize)
    (col : Usize) (hc : col.val ≤ 4) :
    ∃ out, poseidon2.builder_reference.external_owned_loop1 state sums col = ok out := by
  generalize he : 4-col.val = remaining
  induction remaining using Nat.strong_induction_on generalizing sums col with
  | h remaining ih =>
    rw [poseidon2.builder_reference.external_owned_loop1]
    by_cases hit : col.val < 4
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hit),index_ok state col (by simp;omega)]
      simp only [lift,bind_tc_ok]
      have a4 : (Usize.wrapping_add col 4#usize).val = col.val+4 := by rw [uadd _ _ (by simp;omega)];rfl
      have a8 : (Usize.wrapping_add col 8#usize).val = col.val+8 := by rw [uadd _ _ (by simp;omega)];rfl
      have a12 : (Usize.wrapping_add col 12#usize).val = col.val+12 := by rw [uadd _ _ (by simp;omega)];rfl
      rw [index_ok state _ (by rw [a4];simp;omega)]
      simp only [lift,bind_tc_ok]
      rw [index_ok state _ (by rw [a8];simp;omega)]
      simp only [lift,bind_tc_ok]
      rw [index_ok state _ (by rw [a12];simp;omega)]
      simp only [lift,bind_tc_ok]
      rw [BuilderRecordsArray.update_gen _ col _ (by simpa using hit)]
      simp only [lift,bind_tc_ok]
      have hn := BuilderRecordsArray.next_val col (by omega)
      exact ih (4-(Usize.wrapping_add col 1#usize).val) (by omega)
        _ (Usize.wrapping_add col 1#usize) (by omega) rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hit)]
      exact ⟨sums,rfl⟩

#print axioms total
end R1Z.PV_Src_ExternalSums
