import ActualRetainedLowerM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.ActualAllocationNonvacuousM10
open ActualAllocationExtractorM10
open RawRecordedEagerExtractorReadsBin (RunView Coins)
attribute [local irreducible] PublicRecoveryAllocationM10.stageCells

/-- A fully specified view in the ledger's accepted-flag domain. Empty public
bytes exercise a rejecting parser; recovery/cache construction still occurs. -/
@[never_extract,noinline,irreducible] def literalAcceptedRun : RunView := acceptedRun
  { pubBytes := [], initFits := by change 75 ≤ 131072; omega, tag := 0 }
  (fun _ => .payload ⟨[],by change 0 ≤ 3717; omega⟩)

theorem literal_public_bytes : literalAcceptedRun.2.1.1.pubBytes = [] := by
  unfold literalAcceptedRun acceptedRun
  rfl

theorem literal_count (coins : Coins) :
    literalAcceptedRun.2.2 = true ∧
    actualHeap.bits literalAcceptedRun coins = width*cells literalAcceptedRun coins ∧
    3019905024 ≤ actualHeap.bits literalAcceptedRun coins ∧
    0 < actualHeap.bits literalAcceptedRun coins := by
  unfold literalAcceptedRun
  have h := accepted_nonvacuous
    { pubBytes := [], initFits := by change 75 ≤ 131072; omega, tag := 0 }
    (fun _ => .payload ⟨[],by change 0 ≤ 3717; omega⟩) coins
  exact ⟨h.1,h.2.1,ActualRetainedLowerM10.bound _ _,h.2.2⟩

#print axioms literal_public_bytes
#print axioms literal_count
end AspisR1.ActualAllocationNonvacuousM10
end
