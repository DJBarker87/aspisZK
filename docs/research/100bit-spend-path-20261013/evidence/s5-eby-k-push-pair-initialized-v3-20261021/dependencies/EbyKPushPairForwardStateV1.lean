import EbyKConcreteOpsWrapperLawsV1
import EbyKPushStateInvariantStepV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5EbyKPushPairForwardStateV1

open AspisR1WeightsPairCutEbyKDotOpsV1
open AspisR1S5EbyKConcreteOpsInstanceV1
open AspisR1S5EbyKConcreteOpsWrapperLawsV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps := sourceOps

abbrev CutState := AspisR1WeightsPairCut.fast_pairing.EbyKDot
abbrev CutWide := AspisR1WeightsPairCut.field.WideExact
abbrev CutQm := AspisR1WeightsPairCut.field.QM31
abbrev SourceState := AspisR1EbyKPushDotBackend.PushState

/-- The concrete source transition itself supplies the successful class-level
push. The returned class state is the carrier map of that same source output;
no class-wrapper success hypothesis is needed. -/
theorem installed_push_forward_state_step
    (s : CutState) (value : CutWide) (scalar : CutQm)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
      (wideToSource value))
    (hcount : (stateToSource s).count < AspisR1EbyKPushExplicitOpsV1.maxTerms)
    (hscalar : ∀ x ∈
      (AspisR1EbyKPushDotBackend.scalarQ (qToSource scalar)).val,
      x.val < 2147483647)
    (hinv0 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource s).count.val (stateToSource s).c0.sums)
    (hinv1 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource s).count.val (stateToSource s).c1.sums) :
    ∃ sourceOut : SourceState,
      AspisR1WeightsPairCut.fast_pairing.EbyKDot.push s value scalar =
        .ok (.Ok (), stateFromSource sourceOut) ∧
      AspisR1FinishDotCountBoundV2.sumsBelowCount
        sourceOut.count.val sourceOut.c0.sums ∧
      AspisR1FinishDotCountBoundV2.sumsBelowCount
        sourceOut.count.val sourceOut.c1.sums ∧
      sourceOut.count.val = (stateToSource s).count.val + 1 ∧
      AspisR1S5EbyKConcreteOpsWrapperLawsV1.SourcePushUpdate
        (stateToSource s) sourceOut (wideToSource value) (qToSource scalar) := by
  obtain ⟨sourceOut, hsource, hinv0', hinv1', hinc, hprod0, hprod1⟩ :=
    AspisR1S5EbyKPushStateInvariantStepV1.push_success_state_step
      (stateToSource s) (wideToSource value) (qToSource scalar)
      hcanonical hcount hscalar hinv0 hinv1
  have hsource' : AspisR1EbyKPushDotBackend.pushWithDotBackend
      AspisR1EbyKPushDecodedProductUpdate.QRaw
      (stateToSource s) (wideToSource value) (qToSource scalar) =
        .ok (.Ok (), sourceOut) := by
    change AspisR1EbyKPushDotBackend.pushWithDotBackend
      AspisR1S5EbyKPushTotalityV1.QRaw
      (stateToSource s) (wideToSource value) (qToSource scalar) =
        .ok (.Ok (), sourceOut)
    exact hsource
  have hclass : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push s value scalar =
      .ok (.Ok (), stateFromSource sourceOut) := by
    change (do
      let (status, sourceNext) ← AspisR1EbyKPushDotBackend.pushWithDotBackend
        AspisR1EbyKPushDecodedProductUpdate.QRaw
        (stateToSource s) (wideToSource value) (qToSource scalar)
      ok (status, stateFromSource sourceNext)) =
        .ok (.Ok (), stateFromSource sourceOut)
    rw [hsource']
    rfl
  exact ⟨sourceOut, hclass, hinv0', hinv1', hinc,
    ⟨hprod0, hprod1⟩⟩

#print axioms installed_push_forward_state_step
end AspisR1S5EbyKPushPairForwardStateV1
