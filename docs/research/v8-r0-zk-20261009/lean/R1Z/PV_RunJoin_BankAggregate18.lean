import R1Z.PV_RunJoin_BankReads18
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankAggregate18
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

def columns (banks : pair_forest_copy_builder.CopyBanks) (block : Usize) : PV_RunJoin_BankRow17.Columns :=
  if 34 ≤ block.val ∧ block.val < 54 then banks.late else banks.stable

/-- Structural aggregation only: each of the 57 concrete block certificates
is a named premise until independently constructed. -/
theorem loop (banks : pair_forest_copy_builder.CopyBanks)
    (blocks : ∀ block : Usize, block.val < 57 →
      pair_forest_trace.validate_forest_poseidon_block (columns banks block) block = ok (.Ok ()))
    (block : Usize) (hb : block.val ≤ 57) :
    pair_forest_trace.validate_forest_poseidon_rows_loop banks (.Ok ()) block = ok (.Ok ()) := by
  generalize hremaining : 57-block.val = remaining
  induction remaining using Nat.strong_induction_on generalizing block with
  | h remaining ih =>
    rw [pair_forest_trace.validate_forest_poseidon_rows_loop]
    by_cases hlt : block.val < 57
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hlt)]
      simp only [core.result.Result.is_ok,bind_tc_ok,if_true]
      simp only [BuilderForestStdPort.core.ops.range.Range.contains]
      rw [BuilderBankShape.range_usize]
      simp only [bind_tc_ok,UScalar.ofNatCore_val_eq]
      by_cases hc : 34 ≤ block.val ∧ block.val < 54
      · simp [hc]
        have hp := blocks block hlt
        simp [columns,hc] at hp
        rw [hp]
        simp only [bind_tc_ok,lift]
        have hv : (Usize.wrapping_add block 1#usize).val = block.val+1 := by
          rw [uadd _ _ (by simp;omega)]
          rfl
        exact ih _ (by omega) _ (by omega) rfl
      · simp [hc]
        have hp := blocks block hlt
        simp [columns,hc] at hp
        rw [hp]
        simp only [bind_tc_ok,lift]
        have hv : (Usize.wrapping_add block 1#usize).val = block.val+1 := by
          rw [uadd _ _ (by simp;omega)]
          rfl
        exact ih _ (by omega) _ (by omega) rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hlt)]
#print axioms loop

theorem rows (banks : pair_forest_copy_builder.CopyBanks)
    (blocks : ∀ block : Usize, block.val < 57 →
      pair_forest_trace.validate_forest_poseidon_block (columns banks block) block = ok (.Ok ())) :
    pair_forest_trace.validate_forest_poseidon_rows banks = ok (.Ok ()) :=
  loop banks blocks 0#usize (by simp)
#print axioms rows
end R1Z.PV_RunJoin_BankAggregate18
