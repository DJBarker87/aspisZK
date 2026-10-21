import EbyKConcreteOpsWrapperLawsV1
import EbyKPushStateInvariantStepV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5EbyKPushPairWrapperStepV1

open AspisR1WeightsPairCutEbyKDotOpsV1
open AspisR1S5EbyKConcreteOpsInstanceV1
open AspisR1S5EbyKConcreteOpsWrapperLawsV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps := sourceOps

abbrev CutState := AspisR1WeightsPairCut.fast_pairing.EbyKDot
abbrev CutWide := AspisR1WeightsPairCut.field.WideExact
abbrev CutQm := AspisR1WeightsPairCut.field.QM31
abbrev SourceState := AspisR1EbyKPushDotBackend.PushState
abbrev SourceWide := AspisR1EbyKPushDotBackend.PushWide
abbrev SourceQm := AspisR1EbyKPushDotBackend.PushQm

/-- The actual typed EbyKDot class wrapper's successful push is the same
source-model transition, and its returned nominal Pair-cut state inherits the
same count invariant and exact product update. All facts refer to the one
returned state. -/
theorem installed_push_state_step
    (s : CutState) (value : CutWide) (scalar : CutQm) (out : CutState)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
      (wideToSource value))
    (hcount : (stateToSource s).count < AspisR1EbyKPushExplicitOpsV1.maxTerms)
    (hscalar : ∀ x ∈
      (AspisR1EbyKPushDotBackend.scalarQ (qToSource scalar)).val,
      x.val < 2147483647)
    (hinv0 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource s).count.val (stateToSource s).c0.sums)
    (hinv1 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource s).count.val (stateToSource s).c1.sums)
    (hpush : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push s value scalar =
      .ok (.Ok (), out)) :
    ∃ sourceOut : SourceState,
      sourceOps.push (stateToSource s) (wideToSource value) (qToSource scalar) =
        .ok (.Ok (), sourceOut) ∧
      stateFromSource sourceOut = out ∧
      AspisR1FinishDotCountBoundV2.sumsBelowCount out.count.val out.c0.sums ∧
      AspisR1FinishDotCountBoundV2.sumsBelowCount out.count.val out.c1.sums ∧
      out.count.val = (stateToSource s).count.val + 1 ∧
      AspisR1EbyKPushDecodedProductUpdate.castSums sourceOut.c0.sums =
        AspisR1EbyKPushDecodedProductUpdate.tupleAdd
          (AspisR1EbyKPushDecodedProductUpdate.castSums (stateToSource s).c0.sums)
          (AspisR1.R22RawQmProductResidues.qmulCoefficients
            (((wideToSource value).c0.c0.a.val,(wideToSource value).c0.c0.b.val),
             ((wideToSource value).c0.c1.a.val,(wideToSource value).c0.c1.b.val))
            (((qToSource scalar).c0.a.val,(qToSource scalar).c0.b.val),
             ((qToSource scalar).c1.a.val,(qToSource scalar).c1.b.val))) ∧
      AspisR1EbyKPushDecodedProductUpdate.castSums sourceOut.c1.sums =
        AspisR1EbyKPushDecodedProductUpdate.tupleAdd
          (AspisR1EbyKPushDecodedProductUpdate.castSums (stateToSource s).c1.sums)
          (AspisR1.R22RawQmProductResidues.qmulCoefficients
            (((wideToSource value).c1.c0.a.val,(wideToSource value).c1.c0.b.val),
             ((wideToSource value).c1.c1.a.val,(wideToSource value).c1.c1.b.val))
            (((qToSource scalar).c0.a.val,(qToSource scalar).c0.b.val),
             ((qToSource scalar).c1.a.val,(qToSource scalar).c1.b.val))) := by
  obtain ⟨sourceOut, hsource, hmap⟩ :=
    installed_push_success_map s value scalar (.Ok ()) out hpush
  obtain ⟨stepOut, hstep, hout0, hout1, hinc, hprod0, hprod1⟩ :=
    AspisR1S5EbyKPushStateInvariantStepV1.push_success_state_step
      (stateToSource s) (wideToSource value) (qToSource scalar) hcanonical
      hcount hscalar hinv0 hinv1
  have hsource' : sourceOps.push (stateToSource s)
      (wideToSource value) (qToSource scalar) = .ok (.Ok (), sourceOut) := by
    simpa [sourceOps] using hsource
  have hstep' : sourceOps.push (stateToSource s) (wideToSource value)
      (qToSource scalar) = .ok (.Ok (), stepOut) := by
    simpa [sourceOps] using hstep
  have hboth :
      (.ok (.Ok (), sourceOut) : Result ((core.result.Result Unit Unit) × SourceState)) =
        .ok (.Ok (), stepOut) := hsource'.symm.trans hstep'
  have hsame : sourceOut = stepOut := congrArg Prod.snd (Result.ok.inj hboth)
  subst stepOut
  have hout0' : AspisR1FinishDotCountBoundV2.sumsBelowCount out.count.val out.c0.sums := by
    rw [← hmap]
    exact hout0
  have hout1' : AspisR1FinishDotCountBoundV2.sumsBelowCount out.count.val out.c1.sums := by
    rw [← hmap]
    exact hout1
  have hinc' : out.count.val = (stateToSource s).count.val + 1 := by
    rw [← hmap]
    exact hinc
  exact ⟨sourceOut, hsource', hmap, hout0', hout1', hinc', hprod0, hprod1⟩

#print axioms installed_push_state_step
end AspisR1S5EbyKPushPairWrapperStepV1
