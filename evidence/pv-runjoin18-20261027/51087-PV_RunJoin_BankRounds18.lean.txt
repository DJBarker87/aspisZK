import R1Z.PV_RunJoin_BankRow17
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankRounds18
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_BankRow17
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
abbrev Check := core.result.Result Unit pair_trace.PoolV1PairTraceErrorV1

/-- Compose eleven checked round pairs and their actual row checks without
normalizing any Poseidon arithmetic. The hypotheses still need fixture instances. -/
theorem rounds (columns : Columns) (block : Usize) (state : Nat → State)
    (pair : ∀ n : Usize, n.val < 11 → ∃ first,
      poseidon2.evaluate_trace_round_pair (state n.val) n = ok (some (first,state (n.val+1))))
    (reads : ∀ n : Usize, n.val < 11 → ∀ lane : Usize, lane.val < 16 →
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
        columns.val[lane.val]! (rowIndex block (Usize.wrapping_add n 1#usize)) =
          ok (state (n.val+1)).val[lane.val]!)
    (n : Usize) (hn : n.val ≤ 11) :
    pair_forest_trace.validate_forest_poseidon_block_loop1 columns block (state n.val) (.Ok ()) n = ok (.Ok ()) := by
  generalize hremaining : 11-n.val = remaining
  induction remaining using Nat.strong_induction_on generalizing n with
  | h remaining ih =>
    rw [pair_forest_trace.validate_forest_poseidon_block_loop1]
    by_cases hlt : n.val < 11
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hlt)]
      simp only [core.result.Result.is_ok,bind_tc_ok,Bool.true_eq,if_true]
      obtain ⟨first,hp⟩ := pair n hlt
      rw [hp]
      simp only [bind_tc_ok,lift]
      rw [PV_RunJoin_BankRow17.row columns block (Usize.wrapping_add n 1#usize) _ (reads n hlt)]
      simp only [bind_tc_ok]
      have hv := BuilderRecordsArray.next_val n (by omega)
      have hs : state (n.val+1) = state (Usize.wrapping_add n 1#usize).val := by rw [hv]
      rw [hs]
      exact ih _ (by omega) _ (by omega) rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hlt)]
#print axioms rounds

/-- The three padding rows are zero. No recurrence or whole-bank evaluation. -/
theorem padding (columns : Columns) (block : Usize)
    (reads : ∀ n : Usize, 13 ≤ n.val → n.val < 16 → ∀ lane : Usize, lane.val < 16 →
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
        columns.val[lane.val]! (rowIndex block n) =
          ok (Array.repeat 16#usize aspis_core.field.M31.ZERO).val[lane.val]!)
    (n : Usize) (hlo : 13 ≤ n.val) (hhi : n.val ≤ 16) :
    pair_forest_trace.validate_forest_poseidon_block_loop2 columns block (.Ok ()) n = ok (.Ok ()) := by
  generalize hremaining : 16-n.val = remaining
  induction remaining using Nat.strong_induction_on generalizing n with
  | h remaining ih =>
    rw [pair_forest_trace.validate_forest_poseidon_block_loop2]
    by_cases hlt : n.val < 16
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hlt)]
      simp only [core.result.Result.is_ok,bind_tc_ok,Bool.true_eq,if_true]
      rw [PV_RunJoin_BankRow17.row columns block n _ (reads n hlo hlt)]
      simp only [bind_tc_ok,lift]
      have hv := BuilderRecordsArray.next_val n (by omega)
      exact ih _ (by omega) _ (by omega) (by omega) rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hlt)]
#print axioms padding
end R1Z.PV_RunJoin_BankRounds18
