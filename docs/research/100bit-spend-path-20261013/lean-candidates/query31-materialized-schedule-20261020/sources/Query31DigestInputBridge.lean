import Query31SourceCalls
import ExtractedSourceDigestOracle

open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section

namespace AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1PublicPreparation
open TranscriptStep SourceDigestOracle SourceDigestAddresses

/-- The extracted `to_slice` grouping is exactly the retained transcript
`readParts` grouping, before interpreting the digest call. -/
theorem digestCall_input_eq_readParts {H : Type} {D : aspis_core.Digest32 H}
    {hash : H} (c : DigestCall D hash) :
    c.input = TranscriptStep.readParts c.state c.tag := by
  rcases c with ⟨state, tag, stateSlice, tagSlice, input, output,
    hstate, htag, hinput, hdigest⟩
  simp only [lift, Result.ok.injEq] at hstate htag hinput
  subst stateSlice
  subst tagSlice
  subst input
  rfl

#print axioms digestCall_input_eq_readParts

end AspisR1PublicPreparation.Query31SourceSchedule
end
