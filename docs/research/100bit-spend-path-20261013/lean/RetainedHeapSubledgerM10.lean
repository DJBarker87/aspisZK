import PublicRetainedAllocationM10
import CostedAllocationLedgerM10

/-! A concrete always-executed subledger tied to the public/cache stage.
This is NOT actualHeap: cumulative arithmetic/parser/recovery allocations are
absent. The endpoint must not use this as a replacement for allocation adequacy.
Its purpose is to isolate and certify the known nonzero source contribution. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RetainedHeapSubledgerM10
open CostedAllocationLedgerM10
open RawRecordedEagerExtractorReadsBin (RunView Coins)
attribute [local irreducible] BinPublicRecoverySharedStageM10.stage PublicParserWork.parsePublic

def retainedHeap : HeapMirror := ⟨fun run _ => ((PublicRetainedAllocationM10.spec 0).allocation run).bits⟩

theorem public_work_le (run : RunView) (coins : Coins) :
    (BinPublicRecoverySharedStageM10.stage run).2 ≤
    (CostedExtractorStagesM10.eval InitialPublicImageWorkM10.image InitialPublicImageWorkM10.budget
      InitialPublicImageWorkM10.bounded run coins).2 := by
  unfold CostedExtractorStagesM10.eval ExtractorStagesM10.publicStage
  dsimp only
  omega

theorem bits_le_work (run : RunView) (coins : Coins) :
    retainedHeap.bits run coins ≤ PublicRetainedAllocationM10.width*
      (CostedExtractorStagesM10.eval InitialPublicImageWorkM10.image InitialPublicImageWorkM10.budget
        InitialPublicImageWorkM10.bounded run coins).2 := by
  have h := PublicRetainedAllocationM10.work_dominates 0 run
  have hw : ((PublicRetainedAllocationM10.spec 0).run run).2 =
      (BinPublicRecoverySharedStageM10.stage run).2 := by
    unfold PublicRetainedAllocationM10.spec
    rfl
  apply h.trans
  rw [hw]
  exact Nat.mul_le_mul_left _ (public_work_le run coins)

theorem linear_bound (run : RunView) (coins : Coins) :
    retainedHeap.bits run coins ≤ (PublicRetainedAllocationM10.width*workConstant)*(run.1.length+1) := by
  have h := (bits_le_work run coins).trans (Nat.mul_le_mul_left _ (work_bound run coins))
  simpa only [Nat.mul_assoc] using h

/-- Exact count on every view, with no acceptance or log-length hypothesis. -/
theorem exact_bits (run : RunView) (coins : Coins) :
    retainedHeap.bits run coins = 3019905024 :=
  (PublicRetainedAllocationM10.exact_count 0 run).2

theorem positive (run : RunView) (coins : Coins) : 0 < retainedHeap.bits run coins := by
  rw [exact_bits]
  omega

/-- An explicit accepted-flag view in the original ledger domain. This is not
a theorem that an actual protocol experiment returns that view. -/
def acceptedView (pub : RawCutProverCompiler.Public) (proof : RawCutProverCompiler.Proof) : RunView :=
  ([],((pub,proof),true))

theorem accepted_view_nonzero (pub : RawCutProverCompiler.Public)
    (proof : RawCutProverCompiler.Proof) (coins : Coins) :
    (acceptedView pub proof).2.2 = true ∧
    (acceptedView pub proof).1.length = 0 ∧
    retainedHeap.bits (acceptedView pub proof) coins = 3019905024 ∧
    0 < retainedHeap.bits (acceptedView pub proof) coins :=
  ⟨rfl,rfl,exact_bits _ _,positive _ _⟩

#print axioms public_work_le
#print axioms bits_le_work
#print axioms linear_bound
#print axioms exact_bits
#print axioms positive
#print axioms accepted_view_nonzero
end AspisR1.RetainedHeapSubledgerM10
end
