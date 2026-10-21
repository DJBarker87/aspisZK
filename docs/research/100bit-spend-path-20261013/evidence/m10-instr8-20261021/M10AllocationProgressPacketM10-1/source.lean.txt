import AllocationStageCompositionLawsM10
import GSPointRetainedAllocationM10
import RetainedHeapSubledgerM10
import AllocationAdequacyObstructionM10

/-! One final additive packet check. This certificate covers a nonzero retained
subledger, not complete source allocation adequacy or final M10 soundness. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.M10AllocationProgressPacketM10
open RawRecordedEagerExtractorReadsBin (RunView Coins)
open RetainedHeapSubledgerM10

theorem certificate (run : RunView) (coins : Coins) :
    retainedHeap.bits run coins = 3019905024 ∧
    0 < retainedHeap.bits run coins ∧
    retainedHeap.bits run coins ≤ (1024*CostedAllocationLedgerM10.workConstant)*(run.1.length+1) :=
  ⟨exact_bits run coins,positive run coins,linear_bound run coins⟩

#print axioms certificate
end AspisR1.M10AllocationProgressPacketM10
end
