import R1FinalSoundnessBinPerQueryM10
import StagePackM10

/-! Single final import replay of the additive focused packet after every
component and endpoint passed. This is not the global frozen release build. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.M10InstrumentationPacketM10
open CostedAllocationLedgerM10

theorem certificate (heap : HeapMirror) (Q : Nat) (h_M10_allocation : AllocationBound heap Q) :
    RawExtractorCostComposedBin.LedgerRefinement (extractor heap) (params Q) Q ∧
    RawExtractorParameterPolynomial.CoordinateBound (params Q)
      (Q+RawExtractorFixedCubicM10.slack fixed) fixed.overheadConstant 3 ∧
    costPolynomial.natDegree ≤ 3 :=
  ⟨ledger heap Q h_M10_allocation,uniform Q,polynomial_degree⟩

#print axioms certificate
end AspisR1.M10InstrumentationPacketM10
end
