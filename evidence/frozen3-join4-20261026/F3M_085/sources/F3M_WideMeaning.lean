import F3K_WideEncoding
import F3L_SourceNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_WideMeaning
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

theorem limbs (xs : StrictWideByteCodec.WideLimbs) :
    decode (toClaimE (F3K_WideEncoding.prepFromParsed (CandidateWideParserRefinement.limbsToCandidate xs)))=
      WideExactLimbCodec.pairExactEquiv xs := by
  rfl

#print axioms limbs
end AspisR1.F3M_WideMeaning
end
