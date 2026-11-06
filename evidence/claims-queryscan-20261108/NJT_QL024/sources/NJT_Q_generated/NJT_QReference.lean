import NJT_QBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_QReference
open Aeneas Aeneas.Std Result NJT_QBase

/-- The native NCO reference is the literal frozen block_rank body with only
its identifier changed (NJT_Q_REF_IDENTITY.json), so its retained emitted
owner is reused here. No new extraction or handwritten emitted replacement.
The std-operation owner and full Result are exactly those of the cohort. -/
abbrev extractedRankReference := AspisR1QueryScanUnrolled.r0_transcript.block_rank

theorem reference_correct (b : Bytes) : extractedRankReference b=ok (rank b) :=
 rank_source b

#print axioms reference_correct
#check @reference_correct
end AspisR1.NJT_QReference
end
