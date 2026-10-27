import RPz7_Par_Public
set_option autoImplicit false
noncomputable section
namespace AspisR1.Par_Transcript
open Aeneas Aeneas.Std Result
open DrvC_Installation S2W_NativeConsolidation MultiproofConeCanonical

/-- For a transcript associated with this accepted public slice, derive L153
from the source cut, without using the transcript's initFits field. The byte
association is the existing physical/model boundary, not discharged here. -/
theorem accepted_initFits {F C : Type} (c : Configuration F C)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut) (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s)
    (tr : RawCutTranscriptRun.ErasedPrefix)
    (same : tr.statement.pubBytes = bytesOf f.pub.val) :
    tr.statement.pubBytes.length = 1880 ∧
    75 + tr.statement.pubBytes.length ≤ SelectedTranscriptParams.L := by
  rw [same]
  exact Par_Public.accepted_public_bound c accounts1 accounts2 saved f s cuts

#print axioms accepted_initFits
end AspisR1.Par_Transcript
end
