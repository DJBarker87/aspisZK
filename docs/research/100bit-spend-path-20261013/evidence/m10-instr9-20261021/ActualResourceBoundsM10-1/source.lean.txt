import ActualResourceEvalM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.ActualResourceBoundsM10
open RawRecordedEagerExtractorReadsBin (RunView Coins)
open ActualAllocationExtractorM10 (actualHeap)
attribute [local irreducible] BinEagerWordsReads.words

theorem total (Q : Nat) (run : RunView) (coins : Coins) (ha : run.2.2 = true)
    (hl : run.1.length ≤ Q+1161) :
    (ActualResourceEvalM10.eval run coins).2.total ≤ 4*CostedAllocationLedgerM10.scale^3*(run.1.length+1)^3 := by
  change (ActualResourceEvalM10.eval run coins).2.total ≤ _
  unfold ActualResourceEvalM10.eval CostedAllocationLedgerM10.scale
  exact CubicAllocationLiftM10.total_bound _ _ _ _ _ _ _
    (ActualAllocationExtractorM10.work run coins) (BinEagerWordsReads.words_reads run)
    (ActualAllocationExtractorM10.allocation_bound Q run coins ha hl)

theorem field_bound (run : RunView) (coins : Coins) :
    (ActualResourceEvalM10.eval run coins).2.fieldOps ≤ 4*CostedAllocationLedgerM10.scale^3*(run.1.length+1)^3 := by
  change (ActualResourceEvalM10.eval run coins).2.fieldOps ≤ _
  unfold ActualResourceEvalM10.eval CubicAllocationLiftM10.resources
  change (ActualAllocationExtractorM10.eval run coins).2 ≤ _
  unfold CostedAllocationLedgerM10.scale
  exact CubicFieldBoundM10.bound _ _ _ _ _ (ActualAllocationExtractorM10.work run coins)

#print axioms total
#print axioms field_bound
end AspisR1.ActualResourceBoundsM10
end
