import F3K_WideEncoding
import F3L_SourceNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_WideMeaning
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

theorem limbs (xs : StrictWideByteCodec.WideLimbs) :
    decode (toClaimE (F3K_WideEncoding.prepFromParsed (CandidateWideParserRefinement.limbsToCandidate xs)))=
      WideExactLimbCodec.pairExactEquiv xs := by
  have limb (x : RetainedFieldByteCodec.M31Value) :
      (x.val : AspisV8R15.ExactTowerBase.M31Exact)=RetainedExactLimbCodec.m31ResidueEquiv x := by
    apply ZMod.val_injective AspisV8R15.ExactTowerBase.P
    change (x.val : ZMod AspisV8R15.ExactTowerBase.P).val=x.val
    exact ZMod.val_natCast_of_lt x.isLt
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · exact limb (xs.1 0)
      · exact limb (xs.1 1)
    · apply QuadraticAlgebra.ext
      · exact limb (xs.1 2)
      · exact limb (xs.1 3)
  · apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · exact limb (xs.2 0)
      · exact limb (xs.2 1)
    · apply QuadraticAlgebra.ext
      · exact limb (xs.2 2)
      · exact limb (xs.2 3)

#print axioms limbs
end AspisR1.F3M_WideMeaning
end
