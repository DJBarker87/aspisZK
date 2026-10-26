import R1Z.PV_Src_ExternalSums

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalLanes
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open AspisBuilderPoseidonReference PV_Src_ExternalReduce

theorem total (state : Array U32 16#usize) (sums : Array U64 4#usize)
    (lane : Usize) (hl : lane.val ≤ 16) :
    ∃ out, poseidon2.builder_reference.external_owned_loop2 state sums lane = ok out := by
  generalize he : 16-lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing state lane with
  | h remaining ih =>
    rw [poseidon2.builder_reference.external_owned_loop2]
    by_cases hit : lane.val < 16
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hit),index_ok state lane (by simpa using hit)]
      simp only [lift,bind_tc_ok]
      rw [rem_ok lane 4#usize (by simp)]
      simp only [bind_tc_ok]
      have hm : (⟨BitVec.umod lane.bv (4#usize : Usize).bv⟩ : Usize).val < 4 := by
        rw [umod_val]
        exact Nat.mod_lt _ (by decide)
      rw [index_ok_gen sums _ (by simpa using hm)]
      simp only [lift,bind_tc_ok]
      obtain ⟨m,hm⟩ := reduce_total (U64.wrapping_add (UScalar.cast .U64 state.val[lane.val]!)
        sums.val[(⟨BitVec.umod lane.bv (4#usize : Usize).bv⟩ : Usize).val]!)
      rw [hm]
      simp only [bind_tc_ok]
      rw [update_ok _ lane _ (by simpa using hit)]
      simp only [lift,bind_tc_ok]
      have hn := BuilderRecordsArray.next_val lane (by omega)
      exact ih (16-(Usize.wrapping_add lane 1#usize).val) (by omega)
        _ (Usize.wrapping_add lane 1#usize) (by omega) rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hit)]
      exact ⟨state,rfl⟩

#print axioms total
end R1Z.PV_Src_ExternalLanes
