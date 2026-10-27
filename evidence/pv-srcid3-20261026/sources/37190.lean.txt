import R1Z.PV_Src_ExternalReduce

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalBlocks
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderPoseidonReference PV_Src_ExternalReduce

theorem total (state : Array U32 16#usize) (block : Usize) (hb : block.val ≤ 4) :
    ∃ out, poseidon2.builder_reference.external_owned_loop0 state block = ok out := by
  generalize he : 4-block.val = remaining
  induction remaining using Nat.strong_induction_on generalizing state block with
  | h remaining ih =>
    rw [poseidon2.builder_reference.external_owned_loop0]
    by_cases hit : block.val < 4
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hit)]
      simp only [lift,bind_tc_ok]
      have base : (Usize.wrapping_mul block 4#usize).val = block.val*4 := by
        rw [umul _ _ (by simp; omega)];rfl
      have add1 : (Usize.wrapping_add (Usize.wrapping_mul block 4#usize) 1#usize).val = block.val*4+1 := by
        rw [uadd _ _ (by rw [base];simp;omega),base];rfl
      have add2 : (Usize.wrapping_add (Usize.wrapping_mul block 4#usize) 2#usize).val = block.val*4+2 := by
        rw [uadd _ _ (by rw [base];simp;omega),base];rfl
      have add3 : (Usize.wrapping_add (Usize.wrapping_mul block 4#usize) 3#usize).val = block.val*4+3 := by
        rw [uadd _ _ (by rw [base];simp;omega),base];rfl
      rw [index_ok state _ (by rw [base];simp;omega)]
      simp only [lift,bind_tc_ok]
      rw [index_ok state _ (by rw [add1];simp;omega)]
      simp only [lift,bind_tc_ok]
      rw [index_ok state _ (by rw [add2];simp;omega)]
      simp only [lift,bind_tc_ok]
      rw [index_ok state _ (by rw [add3];simp;omega)]
      simp only [lift,bind_tc_ok]
      obtain ⟨x,hx⟩ := mat4_total (Array.make 4#usize
        [state.val[(Usize.wrapping_mul block 4#usize).val]!,
         state.val[(Usize.wrapping_add (Usize.wrapping_mul block 4#usize) 1#usize).val]!,
         state.val[(Usize.wrapping_add (Usize.wrapping_mul block 4#usize) 2#usize).val]!,
         state.val[(Usize.wrapping_add (Usize.wrapping_mul block 4#usize) 3#usize).val]!])
      rw [hx]
      simp only [bind_tc_ok]
      rw [index_ok x 0#usize (by decide)]
      simp only [bind_tc_ok]
      rw [update_ok _ _ _ (by rw [base];simp;omega)]
      simp only [bind_tc_ok]
      rw [index_ok x 1#usize (by decide)]
      simp only [lift,bind_tc_ok]
      rw [update_ok _ _ _ (by rw [add1];simp;omega)]
      simp only [bind_tc_ok]
      rw [index_ok x 2#usize (by decide)]
      simp only [lift,bind_tc_ok]
      rw [update_ok _ _ _ (by rw [add2];simp;omega)]
      simp only [bind_tc_ok]
      rw [index_ok x 3#usize (by decide)]
      simp only [lift,bind_tc_ok]
      rw [update_ok _ _ _ (by rw [add3];simp;omega)]
      simp only [lift,bind_tc_ok]
      have hn := BuilderRecordsArray.next_val block (by omega)
      exact ih (4-(Usize.wrapping_add block 1#usize).val) (by omega)
        _ (Usize.wrapping_add block 1#usize) (by omega) rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hit)]
      exact ⟨state,rfl⟩

#print axioms total
end R1Z.PV_Src_ExternalBlocks
