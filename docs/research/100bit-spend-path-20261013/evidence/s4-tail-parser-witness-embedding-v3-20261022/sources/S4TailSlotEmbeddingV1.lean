import FourDotsCurrentQmParserRootV1
import S4TailLiteralProductsRootV1
import AspisV8R17.QM31WordTower
import R1RetainedExactLimbCodec

set_option autoImplicit false
namespace AspisR1FastDotsTailSlotEmbeddingV1

open AspisR1.RetainedFieldByteCodec

private theorem residueEquiv_natCast (x : M31Value) :
    AspisR1.RetainedExactLimbCodec.m31ResidueEquiv x =
      (x.val : AspisV8R15.ExactTowerBase.M31Exact) := by
  apply ZMod.val_injective AspisV8R15.ExactTowerBase.P
  change x.val = (x.val : ZMod AspisV8R15.ExactTowerBase.P).val
  rw [ZMod.val_natCast_of_lt x.isLt]

private theorem valueToU32_cast (x : M31Value) :
    ((AspisR1.M31ParserRefinement.valueToU32 x).val :
      AspisV8R15.ExactTowerBase.M31Exact) =
      AspisR1.RetainedExactLimbCodec.m31ResidueEquiv x := by
  rw [residueEquiv_natCast, AspisR1.M31ParserRefinement.valueToU32_val]

private theorem current_coordinates (limbs : QM31Limbs) :
    (AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent limbs).c0.a.val = (limbs 0).val ∧
    (AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent limbs).c0.b.val = (limbs 1).val ∧
    (AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent limbs).c1.a.val = (limbs 2).val ∧
    (AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent limbs).c1.b.val = (limbs 3).val :=
  AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent_values limbs

/-- The current extracted parser carrier and the retained exact QM31 field
have the same literal embedding into the wide tower. -/
theorem current_qm_embedding (limbs : QM31Limbs) :
    AspisR1FastDotsTailLiteralProductsRootV1.embedQM
      (AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent limbs) =
    (algebraMap AspisV8R15.ExactTowerBase.QM31Exact AspisWideTower.WideExact)
      (AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv limbs) := by
  have h0 : (((AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent limbs).c0.a.val :
      AspisV8R15.ExactTowerBase.M31Exact)) =
      AspisR1.RetainedExactLimbCodec.m31ResidueEquiv (limbs 0) := by
    rw [← valueToU32_cast]
    rfl
  have h1 : (((AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent limbs).c0.b.val :
      AspisV8R15.ExactTowerBase.M31Exact)) =
      AspisR1.RetainedExactLimbCodec.m31ResidueEquiv (limbs 1) := by
    rw [← valueToU32_cast]
    rfl
  have h2 : (((AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent limbs).c1.a.val :
      AspisV8R15.ExactTowerBase.M31Exact)) =
      AspisR1.RetainedExactLimbCodec.m31ResidueEquiv (limbs 2) := by
    rw [← valueToU32_cast]
    rfl
  have h3 : (((AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent limbs).c1.b.val :
      AspisV8R15.ExactTowerBase.M31Exact)) =
      AspisR1.RetainedExactLimbCodec.m31ResidueEquiv (limbs 3) := by
    rw [← valueToU32_cast]
    rfl
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · simpa [AspisR1FastDotsTailLiteralProductsRootV1.embedQM,
          AspisR1FastDotsTailFieldProductRootV1.qmDecoded,
          AspisV8R17.QM31WordTower.decodeQ,
          AspisV8R17.QM31WordTower.embedQ,
          AspisV8R17.QM31WordTower.embedC,
          AspisV8R17.QM31WordResidues.decodeQ,
          AspisV8R17.QM31WordResidues.decodeC,
          AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent,
          AspisR1FastDotsCurrentQmParserRootV1.toCurrent,
          AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv,
          AspisR1.RetainedExactLimbCodec.limbsToQM31Exact] using h0
      · simpa [AspisR1FastDotsTailLiteralProductsRootV1.embedQM,
          AspisR1FastDotsTailFieldProductRootV1.qmDecoded,
          AspisV8R17.QM31WordTower.decodeQ,
          AspisV8R17.QM31WordTower.embedQ,
          AspisV8R17.QM31WordTower.embedC,
          AspisV8R17.QM31WordResidues.decodeQ,
          AspisV8R17.QM31WordResidues.decodeC,
          AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent,
          AspisR1FastDotsCurrentQmParserRootV1.toCurrent,
          AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv,
          AspisR1.RetainedExactLimbCodec.limbsToQM31Exact] using h1
    · apply QuadraticAlgebra.ext
      · simpa [AspisR1FastDotsTailLiteralProductsRootV1.embedQM,
          AspisR1FastDotsTailFieldProductRootV1.qmDecoded,
          AspisV8R17.QM31WordTower.decodeQ,
          AspisV8R17.QM31WordTower.embedQ,
          AspisV8R17.QM31WordTower.embedC,
          AspisV8R17.QM31WordResidues.decodeQ,
          AspisV8R17.QM31WordResidues.decodeC,
          AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent,
          AspisR1FastDotsCurrentQmParserRootV1.toCurrent,
          AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv,
          AspisR1.RetainedExactLimbCodec.limbsToQM31Exact] using h2
      · simpa [AspisR1FastDotsTailLiteralProductsRootV1.embedQM,
          AspisR1FastDotsTailFieldProductRootV1.qmDecoded,
          AspisV8R17.QM31WordTower.decodeQ,
          AspisV8R17.QM31WordTower.embedQ,
          AspisV8R17.QM31WordTower.embedC,
          AspisV8R17.QM31WordResidues.decodeQ,
          AspisV8R17.QM31WordResidues.decodeC,
          AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent,
          AspisR1FastDotsCurrentQmParserRootV1.toCurrent,
          AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv,
          AspisR1.RetainedExactLimbCodec.limbsToQM31Exact] using h3
  · rfl

#print axioms current_qm_embedding
end AspisR1FastDotsTailSlotEmbeddingV1
