import R1Z.PV_Src_ExternalTotal
import R1Z.PV_Src_ScalarReduce

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalCanonical
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open AspisBuilderPoseidonReference PV_Src_ExternalReduce

theorem loop (state : Array U32 16#usize) (sums : Array U64 4#usize)
    (lane : Usize) (hl : lane.val ≤ 16)
    (prior : ∀ j, j < lane.val → state.val[j]!.val < 2147483647) :
    ∃ out, poseidon2.builder_reference.external_owned_loop2 state sums lane = ok out ∧
      ∀ j, j < 16 → out.val[j]!.val < 2147483647 := by
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
      let x := U64.wrapping_add (UScalar.cast .U64 state.val[lane.val]!)
        sums.val[(⟨BitVec.umod lane.bv (4#usize : Usize).bv⟩ : Usize).val]!
      rw [PV_Src_ScalarReduce.reference_eq]
      simp only [bind_tc_ok]
      rw [update_ok _ lane _ (by simpa using hit)]
      simp only [lift,bind_tc_ok]
      have hn := BuilderRecordsArray.next_val lane (by omega)
      apply ih (16-(Usize.wrapping_add lane 1#usize).val) (by omega)
        (state.set lane (PV_Src_ScalarReduce.value x)) (Usize.wrapping_add lane 1#usize) (by omega)
      · intro j hj
        rw [BuilderRecordsArray.set_get _ _ _ _ (by simpa using hit)]
        split
        · exact PV_Src_ScalarReduce.canonical x
        · next hne => exact prior j (by omega)
      · rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hit)]
      exact ⟨state,rfl,fun j hj => prior j (by omega)⟩

theorem total (state : Array U32 16#usize) :
    ∃ out, PV_Src_ExternalReference.run state = ok out ∧
      ∀ j, j < 16 → out.val[j]!.val < 2147483647 := by
  obtain ⟨blocks,hb⟩ := PV_Src_ExternalBlocks.total state 0#usize (by simp)
  obtain ⟨sums,hs⟩ := PV_Src_ExternalSums.total blocks (Array.repeat 4#usize 0#u64) 0#usize (by simp)
  obtain ⟨out,ho,hcanon⟩ := loop blocks sums 0#usize (by simp) (by simp)
  refine ⟨out,?_,hcanon⟩
  rw [PV_Src_ExternalReference.run,poseidon2.builder_reference.external_owned,hb]
  simp only [bind_tc_ok]
  rw [hs]
  simpa only [bind_tc_ok] using ho

#print axioms loop
#print axioms total
end R1Z.PV_Src_ExternalCanonical
