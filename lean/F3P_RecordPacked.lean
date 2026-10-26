import F3P_SemanticClaimsY
import ExtractedRecordStrictCodec
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_RecordPacked
open Aeneas Aeneas.Std
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality ExtractedRecordStrictCodec
open AspisR1CurrentPreparedClaim.Concrete AspisR1CurrentPreparedClaim.ClaimParser

theorem numeric (arr : Array U8 32#usize)
    (hc : ∀ i : Fin 8,(wordLE arr i).val<2147483647) :
    decode (fromFinish (AspisR1CurrentWide.Proof.recordWideToFinish
      (packed (wordLE arr 0) (wordLE arr 1) (wordLE arr 2) (wordLE arr 3)
        (wordLE arr 4) (wordLE arr 5) (wordLE arr 6) (wordLE arr 7))))=
      WideExactLimbCodec.pairExactEquiv (canonicalLimbs arr hc) := by
  have limb (x : U32) (h : x.val<2147483647) :
      (x.val : AspisV8R15.ExactTowerBase.M31Exact)=RetainedExactLimbCodec.m31ResidueEquiv ⟨x.val,h⟩ := by
    apply ZMod.val_injective AspisV8R15.ExactTowerBase.P
    change (x.val : ZMod AspisV8R15.ExactTowerBase.P).val=x.val
    exact ZMod.val_natCast_of_lt h
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · exact limb (wordLE arr 0) (hc 0)
      · exact limb (wordLE arr 1) (hc 1)
    · apply QuadraticAlgebra.ext
      · exact limb (wordLE arr 2) (hc 2)
      · exact limb (wordLE arr 3) (hc 3)
  · apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · exact limb (wordLE arr 4) (hc 4)
      · exact limb (wordLE arr 5) (hc 5)
    · apply QuadraticAlgebra.ext
      · exact limb (wordLE arr 6) (hc 6)
      · exact limb (wordLE arr 7) (hc 7)

#print axioms numeric
end AspisR1.F3P_RecordPacked
end
