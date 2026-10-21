import EbyKConcreteOpsWrapperLawsV1
import S4TailFinishSourceMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5EbyKPushPairFinishForwardV9

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

#print axioms installed_finish_total_canonical_residues
end AspisR1S5EbyKPushPairFinishForwardV9
