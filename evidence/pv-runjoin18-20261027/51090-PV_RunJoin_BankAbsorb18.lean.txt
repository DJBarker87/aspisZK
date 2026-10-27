import R1Z.PV_RunJoin_BankInitial18
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankAbsorb18
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_BankRow17

theorem absorb (columns : Columns) (base : Usize) (state : Nat → State)
    (step : ∀ lane : Usize, lane.val < 8 → ∃ word sum,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
        columns.val[lane.val]! (Usize.wrapping_add base 12#usize) = ok word ∧
      aspis_core.field.M31.add (state lane.val).val[lane.val]! word = ok sum ∧
      (state lane.val).set lane sum = state (lane.val+1))
    (iter : core.ops.range.Range Usize) (he : iter.end = 8#usize) (hi : iter.start.val ≤ 8) :
    pair_forest_trace.validate_forest_poseidon_block_loop0 iter columns base (state iter.start.val) = ok (state 8) := by
  generalize hremaining : 8-iter.start.val = remaining
  induction remaining using Nat.strong_induction_on generalizing iter with
  | h remaining ih =>
    rw [pair_forest_trace.validate_forest_poseidon_block_loop0]
    by_cases hlt : iter.start.val < 8
    · obtain ⟨next,hn,hv,hend⟩ := PV_Src_Forest_BankRange.next_some iter (by simpa [he] using hlt)
      rw [hn]
      simp only [bind_tc_ok,lift]
      rw [index_ok_gen (state iter.start.val) iter.start (by simp;omega)]
      simp only [bind_tc_ok]
      rw [index_ok_gen columns iter.start (by simp;omega)]
      simp only [bind_tc_ok]
      obtain ⟨word,sum,hr,ha,hs⟩ := step iter.start hlt
      rw [hr]
      simp only [bind_tc_ok]
      rw [ha]
      simp only [bind_tc_ok]
      rw [BuilderRecordsArray.update_gen _ iter.start sum (by simp;omega)]
      simp only [bind_tc_ok]
      rw [hs,← hv]
      exact ih _ (by omega) next (hend.trans he) (by omega) rfl
    · rw [PV_Src_Forest_BankRange.next_none iter (by simpa [he] using Nat.le_of_not_gt hlt)]
      have ht : iter.start.val = 8 := by omega
      simp only [bind_tc_ok,ht]
#print axioms absorb
end R1Z.PV_RunJoin_BankAbsorb18
