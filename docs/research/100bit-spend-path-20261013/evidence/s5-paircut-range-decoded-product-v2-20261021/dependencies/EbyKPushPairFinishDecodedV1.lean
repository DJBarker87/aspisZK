import EbyKConcreteOpsWrapperLawsV1
import S4TailFinishSourceMapV1
import S4TailFinishFieldRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5EbyKPushPairFinishDecodedV1

private theorem bind_ok_value {α β : Type} (x : α) (k : α → Result β) :
    (do let y ← (Result.ok x : Result α); k y) = k x := by
  rfl

open AspisR1WeightsPairCutEbyKDotOpsV1
open AspisR1S5EbyKConcreteOpsInstanceV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps := sourceOps

abbrev CutState := AspisR1WeightsPairCut.fast_pairing.EbyKDot
abbrev CurrentWide := AspisR1FastDotsTailFinishSourceMapV1.CurrentWide

/-- The installed Pair-cut EbyK finish wrapper is total on every state. Its
returned current-Wide representation is the exact reducer image of the same
state's two arrays, and the underlying eight field coordinates are canonical. -/
theorem installed_finish_total_canonical_residues (s : CutState) :
    ∃ currentOut : CurrentWide,
      sourceOps.finish (stateToSource s) = .ok currentOut ∧
      AspisR1WeightsPairCut.fast_pairing.EbyKDot.finish s =
        .ok (wideFromSource currentOut) ∧
      ∃ finish : AspisR1FastDotsTailFinishSourceMapV1.FinishE,
        AspisR1FastDotsTailFinishSourceMapV1.finishEToCurrent finish = currentOut ∧
        AspisR1CurrentWide.Proof.CanonicalFinish finish ∧
        AspisR1FastDotsTailFinishSourceMapV1.currentFinishWords currentOut =
          (((stateToSource s).c0.sums.val ++ (stateToSource s).c1.sums.val).map
            AspisR1EbyKFinish.Proof.word) := by
  obtain ⟨currentOut,hfinish,hfinishE⟩ :=
    AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent_total (stateToSource s)
  have hsource : sourceOps.finish (stateToSource s) = .ok currentOut := by
    simpa [sourceOps] using hfinish
  have hclass : AspisR1WeightsPairCut.fast_pairing.EbyKDot.finish s =
      .ok (wideFromSource currentOut) := by
    change (do
      let w ← sourceOps.finish (stateToSource s)
      ok (wideFromSource w)) = .ok (wideFromSource currentOut)
    rw [hsource]
    exact bind_ok_value currentOut (fun w => Result.ok (wideFromSource w))
  exact ⟨currentOut,hsource,hclass,hfinishE⟩


/-- The actual installed class finish result decodes to the state value of the
same concrete source accumulator. The eight output residues are supplied by
the retained source finish theorem and consumed by the exact field decoder
bridge. -/
theorem installed_finish_decoded_state (s : CutState) :
    ∃ currentOut : CurrentWide,
      AspisR1WeightsPairCut.fast_pairing.EbyKDot.finish s =
        .ok (wideFromSource currentOut) ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE currentOut) =
        AspisR1FastDotsTailFieldProductRootV1.decodeState
          (AspisR1FastDotsPushProductTraceRootV1.stateValue (stateToSource s)) := by
  obtain ⟨currentOut, hfinish, hwords⟩ :=
    AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent_total_residue_values
      (stateToSource s)
  have hsource : sourceOps.finish (stateToSource s) = .ok currentOut := by
    simpa [sourceOps] using hfinish
  have hclass : AspisR1WeightsPairCut.fast_pairing.EbyKDot.finish s =
      .ok (wideFromSource currentOut) := by
    change (do
      let w ← sourceOps.finish (stateToSource s)
      ok (wideFromSource w)) = .ok (wideFromSource currentOut)
    rw [hsource]
    exact bind_ok_value currentOut (fun w => Result.ok (wideFromSource w))
  have hdecode := AspisR1FastDotsTailFinishFieldRootV1.finish_words_decode_state
    (stateToSource s) currentOut hwords
  exact ⟨currentOut, hclass, hdecode⟩

#print axioms installed_finish_decoded_state

#print axioms installed_finish_total_canonical_residues
end AspisR1S5EbyKPushPairFinishDecodedV1
