import ActualResourceBoundsM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.ActualLedgerSideBoundsM10
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget
open RawExtractorCostLedger
open RawRecordedEagerExtractorReadsBin (RunView Coins)
open ActualAllocationExtractorM10 (actualHeap)
attribute [local irreducible] BinEagerWordsReads.words

theorem total_overhead (Q : Nat) (run : RunView) (coins : Coins) (ha : run.2.2 = true)
    (hl : run.1.length ≤ Q+1161) : (ActualResourceEvalM10.eval run coins).2.total ≤ (CostedAllocationLedgerM10.params Q).overhead :=
  CostedAllocationLedgerM10.lift_log _ _ Q (ActualResourceBoundsM10.total Q run coins ha hl) hl

theorem bounded_jobs (Q : Nat) (run : RunView) (coins : Coins) (hl : run.1.length ≤ Q+1161) :
    ∃ j : Jobs AspisWideTower.WideExact, j.Bounded (CostedAllocationLedgerM10.params Q).n (CostedAllocationLedgerM10.params Q).b (CostedAllocationLedgerM10.params Q).count ∧
      (ActualResourceEvalM10.eval run coins).2.fieldOps ≤ j.charge (CostedAllocationLedgerM10.params Q).mulBudget+(CostedAllocationLedgerM10.params Q).overhead := by
  obtain ⟨j,hj,_⟩ := CostedAllocationLedgerM10.bounded_jobs actualHeap Q run coins hl
  refine ⟨j,hj,?_⟩
  exact (CostedAllocationLedgerM10.lift_log _ _ Q (ActualResourceBoundsM10.field_bound run coins) hl).trans (Nat.le_add_left _ _)

theorem reads (Q : Nat) (run : RunView) (coins : Coins) (hl : run.1.length ≤ Q+1161) :
    (ActualResourceEvalM10.eval run coins).2.logReads ≤ (CostedAllocationLedgerM10.params Q).readBudget := by
  have hh := (BinEagerWordsReads.words_reads run).trans
    (Nat.mul_le_mul_left 12976224 hl)
  have hb : (CostedAllocationLedgerM10.params Q).readBudget = 7*2000000*(Q+1161) := by
    unfold CostedAllocationLedgerM10.params RawExtractorFixedCubicM10.family
      RawExtractorCostComposedV2.Parameters.readBudget CostedAllocationLedgerM10.fixed
    rfl
  unfold ActualResourceEvalM10.eval CubicAllocationLiftM10.resources
  change (BinEagerWordsReads.words run).2 ≤ (CostedAllocationLedgerM10.params Q).readBudget
  rw [hb]
  exact hh.trans (Nat.mul_le_mul_right (Q+1161) (show 12976224 ≤ 7*2000000 by omega))

#print axioms total_overhead
#print axioms bounded_jobs
#print axioms reads
end AspisR1.ActualLedgerSideBoundsM10
end
