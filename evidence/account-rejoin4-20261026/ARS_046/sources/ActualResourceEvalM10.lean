import ActualAllocationExtractorM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.ActualResourceEvalM10
open RawExtractorCostComposedV2 (Resources)
open RawExtractorCostLedger
open RawRecordedEagerExtractorReadsBin (RunView Coins)
open ActualAllocationExtractorM10 (actualHeap)
attribute [local irreducible] BinEagerWordsReads.words

@[irreducible] def eval (run : RunView) (coins : Coins) : Option SpendRelation.Wspend × Resources :=
  let x := ActualAllocationExtractorM10.eval run coins
  (x.1,CubicAllocationLiftM10.resources x.2 (BinEagerWordsReads.words run).2
    (actualHeap.bits run coins) run.1.length CostedAllocationLedgerM10.naturalConstant)

theorem value (run : RunView) (coins : Coins) :
    (eval run coins).1 = RawRecordedPublicSpendExtractorBin.extract run coins := by
  unfold eval
  exact ActualAllocationExtractorM10.value run coins

#print axioms value
end AspisR1.ActualResourceEvalM10
end
