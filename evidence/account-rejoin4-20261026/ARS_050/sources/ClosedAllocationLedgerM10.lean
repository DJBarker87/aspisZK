import ActualCostedExtractorM10
import ActualLedgerSideBoundsM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.ClosedAllocationLedgerM10
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget
open RawExtractorCostComposedV2 (Resources)
open RawExtractorCostLedger
open RawRecordedEagerExtractorReadsBin (RunView Coins)
attribute [local irreducible] BinEagerWordsReads.words

theorem ledger (Q : Nat) : RawExtractorCostComposedBin.LedgerRefinement ActualCostedExtractorM10.extractor (CostedAllocationLedgerM10.params Q) Q := by
  unfold ActualCostedExtractorM10.extractor
  constructor
  · exact Nat.le_refl _
  · intro run coins _ hl
    exact ActualLedgerSideBoundsM10.bounded_jobs Q run coins hl
  · intro run coins _ hl
    exact ActualLedgerSideBoundsM10.reads Q run coins hl
  · intro run coins ha hl
    have ht := ActualLedgerSideBoundsM10.total_overhead Q run coins ha hl
    have hb : (ActualResourceEvalM10.eval run coins).2.bits ≤ (ActualResourceEvalM10.eval run coins).2.total := by
      unfold Resources.total
      omega
    have hf : 1 ≤ ((CostedAllocationLedgerM10.params Q).b+1)^2 := by
      have hh := Nat.pow_le_pow_left (show 1 ≤ (CostedAllocationLedgerM10.params Q).b+1 by omega) 2
      simpa only [one_pow] using hh
    have hm := Nat.mul_le_mul
      (show (CostedAllocationLedgerM10.params Q).overhead ≤ (ActualResourceEvalM10.eval run coins).2.fieldOps+
        (ActualResourceEvalM10.eval run coins).2.logReads+(CostedAllocationLedgerM10.params Q).overhead by omega) hf
    change (ActualResourceEvalM10.eval run coins).2.bits ≤ _
    exact (hb.trans ht).trans (by simpa only [Nat.mul_one] using hm)

theorem uniform (Q : Nat) : RawExtractorParameterPolynomial.CoordinateBound (CostedAllocationLedgerM10.params Q)
    (Q+RawExtractorFixedCubicM10.slack CostedAllocationLedgerM10.fixed)
    CostedAllocationLedgerM10.fixed.overheadConstant 3 := CostedAllocationLedgerM10.uniform Q

theorem polynomial_eval (Q : Nat) : CostedAllocationLedgerM10.costPolynomial.eval Q = (CostedAllocationLedgerM10.params Q).attemptBudget :=
  CostedAllocationLedgerM10.polynomial_eval Q

theorem polynomial_degree : CostedAllocationLedgerM10.costPolynomial.natDegree ≤ 3 := CostedAllocationLedgerM10.polynomial_degree

theorem accepted_cost (Q : Nat) (run : RunView) (ha : run.2.2 = true)
    (hl : run.1.length ≤ Q+1161) :
    (∀ coins, (ActualCostedExtractorM10.extractor.eval run coins).2.total ≤ CostedAllocationLedgerM10.costPolynomial.eval Q) ∧
    AspisV8R19.OracleResampling.mean (fun coins : Coins =>
      ((ActualCostedExtractorM10.extractor.eval run coins).2.total : ℚ)) ≤ ((CostedAllocationLedgerM10.costPolynomial.eval Q : Nat) : ℚ) := by
  rw [polynomial_eval]
  exact RawExtractorCostComposedBin.accepted_attempt_cost ActualCostedExtractorM10.extractor (CostedAllocationLedgerM10.params Q) Q (ledger Q) run ha hl

theorem direct_bound (Q : Nat) (run : RunView) (coins : Coins) (ha : run.2.2 = true)
    (hl : run.1.length ≤ Q+1161) :
    (ActualResourceEvalM10.eval run coins).2.total ≤ 4*CostedAllocationLedgerM10.scale^3*(Q+1162)^3 :=
  (ActualResourceBoundsM10.total Q run coins ha hl).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))

#print axioms ledger
#print axioms uniform
#print axioms polynomial_eval
#print axioms polynomial_degree
#print axioms accepted_cost
#print axioms direct_bound
end AspisR1.ClosedAllocationLedgerM10
end
