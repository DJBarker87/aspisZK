import R1Z.PV_RunJoin_BankAggregate18
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
namespace R1Z.PV_RunJoin_UniversalBankChecks22
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 BuilderRecordsFields
open PV_RunJoin_BankAggregate18
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
abbrev Check := core.result.Result Unit pair_trace.PoolV1PairTraceErrorV1

theorem error_persists (banks : pair_forest_copy_builder.CopyBanks)
    (error : pair_trace.PoolV1PairTraceErrorV1) (block : Usize) :
    pair_forest_trace.validate_forest_poseidon_rows_loop banks (.Err error) block = ok (.Err error) := by
  rw [pair_forest_trace.validate_forest_poseidon_rows_loop]
  split
  · rfl
  · rfl
#print axioms error_persists

theorem result_ok (banks : pair_forest_copy_builder.CopyBanks) (result : Check) (block : Usize)
    (success : pair_forest_trace.validate_forest_poseidon_rows_loop banks result block = ok (.Ok ())) :
    result = .Ok () := by
  cases result with
  | Ok u => cases u; rfl
  | Err error => rw [error_persists] at success; cases success
#print axioms result_ok

/-- Successful aggregate validation performs the current real block call;
it cannot skip a failed block and recover in a later iteration. -/
theorem step (banks : pair_forest_copy_builder.CopyBanks) (block : Usize) (hb : block.val < 57)
    (success : pair_forest_trace.validate_forest_poseidon_rows_loop banks (.Ok ()) block = ok (.Ok ())) :
    ∃ result : Check,
      pair_forest_trace.validate_forest_poseidon_block (columns banks block) block = ok result ∧
      pair_forest_trace.validate_forest_poseidon_rows_loop banks result
        (Usize.wrapping_add block 1#usize) = ok (.Ok ()) := by
  rw [pair_forest_trace.validate_forest_poseidon_rows_loop] at success
  rw [if_pos (by simpa [UScalar.lt_equiv] using hb)] at success
  simp only [core.result.Result.is_ok,bind_tc_ok,if_true,
    BuilderForestStdPort.core.ops.range.Range.contains] at success
  rw [BuilderBankShape.range_usize] at success
  simp only [bind_tc_ok,UScalar.ofNatCore_val_eq] at success
  by_cases hc : 34 ≤ block.val ∧ block.val < 54
  · simp [hc] at success
    obtain ⟨result,hr,hs⟩ := bind_ok_inv success
    exact ⟨result,by simpa [columns,hc] using hr,by simpa [lift,bind_tc_ok] using hs⟩
  · simp [hc] at success
    obtain ⟨result,hr,hs⟩ := bind_ok_inv success
    exact ⟨result,by simpa [columns,hc] using hr,by simpa [lift,bind_tc_ok] using hs⟩
#print axioms step

/-- Every one of the 57 source block validators succeeds whenever the
aggregate succeeds. This is a universal control-flow theorem, not a numeric
certificate or a proof that arbitrary source-generated blocks validate. -/
theorem loop_checks (banks : pair_forest_copy_builder.CopyBanks) (block : Usize)
    (hb : block.val ≤ 57)
    (success : pair_forest_trace.validate_forest_poseidon_rows_loop banks (.Ok ()) block = ok (.Ok ())) :
    ∀ q : Usize, block.val ≤ q.val → q.val < 57 →
      pair_forest_trace.validate_forest_poseidon_block (columns banks q) q = ok (.Ok ()) := by
  generalize hremaining : 57-block.val = remaining
  induction remaining using Nat.strong_induction_on generalizing block with
  | h remaining ih =>
    intro q hge hq
    have hlt : block.val < 57 := by omega
    obtain ⟨result,hr,hs⟩ := step banks block hlt success
    have he := result_ok banks result (Usize.wrapping_add block 1#usize) hs
    subst result
    by_cases hsame : q = block
    · subst q
      exact hr
    · have hv : (Usize.wrapping_add block 1#usize).val = block.val+1 := by
        rw [uadd _ _ (by simp;omega)]
        rfl
      have hn : block.val < q.val := by
        by_contra hn
        have hvq : q.val = block.val := by omega
        exact hsame (UScalar.eq_of_val_eq hvq)
      exact ih _ (by omega) (Usize.wrapping_add block 1#usize) (by omega) hs rfl q (by omega) hq
#print axioms loop_checks

theorem rows_iff (banks : pair_forest_copy_builder.CopyBanks) :
    pair_forest_trace.validate_forest_poseidon_rows banks = ok (.Ok ()) ↔
      ∀ q : Usize, q.val < 57 →
        pair_forest_trace.validate_forest_poseidon_block (columns banks q) q = ok (.Ok ()) := by
  constructor
  · intro success q hq
    exact loop_checks banks 0#usize (by simp) success q (by simp) hq
  · exact PV_RunJoin_BankAggregate18.rows banks
#print axioms rows_iff
end R1Z.PV_RunJoin_UniversalBankChecks22
