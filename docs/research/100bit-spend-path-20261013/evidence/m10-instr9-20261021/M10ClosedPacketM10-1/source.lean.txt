import R1FinalSoundnessBinPerQueryM10Closed
import ActualAllocationNonvacuousM10
import ActualRetainedLowerM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.M10ClosedPacketM10
open RawRecordedEagerExtractorReadsBin (RunView Coins)

theorem certificate :
    (∀ Q, CostedAllocationLedgerM10.AllocationBound ActualAllocationExtractorM10.actualHeap Q) ∧
    (∀ Q, RawExtractorCostComposedBin.LedgerRefinement
      ActualCostedExtractorM10.extractor (CostedAllocationLedgerM10.params Q) Q) ∧
    (∀ run : RunView, ∀ coins : Coins,
      (ActualAllocationExtractorM10.eval run coins).1 = RawRecordedPublicSpendExtractorBin.extract run coins) ∧
    (∀ run : RunView, ∀ coins : Coins, 3019905024 ≤ ActualAllocationExtractorM10.actualHeap.bits run coins) ∧
    CostedAllocationLedgerM10.costPolynomial.natDegree ≤ 3 :=
  ⟨ActualAllocationExtractorM10.allocation_bound,ClosedAllocationLedgerM10.ledger,
    ActualAllocationExtractorM10.value,ActualRetainedLowerM10.bound,ClosedAllocationLedgerM10.polynomial_degree⟩

#print axioms certificate
end AspisR1.M10ClosedPacketM10
end
