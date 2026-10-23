import AspisR1S5ClaimScalarConcreteQRawTrace

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5ClaimScalarEmbeddedProductSum
open AspisR1S5ClaimScalarConcreteQRawTrace
open AspisR1FinishDotReturnedFieldProductV1
open AspisR1CurrentPreparedClaim

abbrev Wide := AspisWideTower.WideExact
abbrev ClaimWide := AspisR1CurrentPreparedClaim.Concrete.E
abbrev ClaimQM := AspisR1S5ClaimScalarConcreteQRawTrace.ClaimQM

def scalarEmbed (q : ClaimQM) : Wide :=
  algebraMap AspisV8R15.ExactTowerBase.QM31Exact Wide
    (AspisR1CurrentWide.Proof.decodeQM
      (AspisR1CurrentPreparedClaim.Concrete.toQM q))

theorem finishQMDecoded_claim (q : ClaimQM) :
    finishQMDecoded
        (AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishQM q) =
      AspisR1CurrentWide.Proof.decodeQM
        (AspisR1CurrentPreparedClaim.Concrete.toQM q) := by
  rw [← finishQM_embed_eq_decode]
  simp [AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishQM,
    AspisR1CurrentWide.Proof.toFinishQM,
    AspisR1CurrentWide.Proof.toFinishCM,
    AspisR1CurrentWide.Proof.decodeQM,
    AspisR1CurrentWide.Proof.toQM,
    AspisR1.ExtractedCurrentQM31Exact.decode,
    AspisR1CurrentWide.Proof.toCM,
    AspisV8R17.QM31WordTower.embedQ,
    AspisV8R17.QM31WordTower.embedC,
    AspisV8R17.QM31WordResidues.decodeQ,
    AspisV8R17.QM31WordResidues.decodeC,
    AspisR1FinishDotReturnedFieldProductV1.finishQMResiduesQ,
    AspisR1FinishDotReturnedFieldProductV1.finishQMResidues]
  rfl

theorem claimToFinishE_c0_decode (x : ClaimWide) :
    finishQMDecoded (AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishE x).c0 =
      (Concrete.decode x).re := by
  change finishQMDecoded
      (AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishQM x.c0) =
    AspisR1CurrentWide.Proof.decodeQM (Concrete.toQM x.c0)
  exact finishQMDecoded_claim x.c0

theorem claimToFinishE_c1_decode (x : ClaimWide) :
    finishQMDecoded (AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishE x).c1 =
      (Concrete.decode x).im := by
  change finishQMDecoded
      (AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishQM x.c1) =
    AspisR1CurrentWide.Proof.decodeQM (Concrete.toQM x.c1)
  exact finishQMDecoded_claim x.c1

theorem queryProductWide_eq_decode_mul_scalar
    (x : ClaimWide) (q : ClaimQM) :
    queryProductWide
      (AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishE x)
      (AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishQM q) =
      Concrete.decode x * scalarEmbed q := by
  unfold queryProductWide scalarEmbed
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re]
    rw [claimToFinishE_c0_decode, finishQMDecoded_claim]
    simp
    rfl
  · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.algebraMap_im]
    rw [claimToFinishE_c1_decode, finishQMDecoded_claim]
    simp
    rfl

theorem productSum_finishRows_eq_scalarEmbedded_sum
    (xs : List (Usize × ClaimWide × ClaimQM)) :
    AspisR1FinishDotReturnedFieldProductV1.productSum (finishRows xs) =
      (xs.map (fun t => Concrete.decode t.2.1 * scalarEmbed t.2.2)).sum := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
      change queryProductWide
          (AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishE t.2.1)
          (AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishQM t.2.2) +
        AspisR1FinishDotReturnedFieldProductV1.productSum (finishRows xs) =
        Concrete.decode t.2.1 * scalarEmbed t.2.2 +
          (xs.map (fun t => Concrete.decode t.2.1 * scalarEmbed t.2.2)).sum
      rw [queryProductWide_eq_decode_mul_scalar, ih]

#print axioms queryProductWide_eq_decode_mul_scalar
#print axioms productSum_finishRows_eq_scalarEmbedded_sum
end AspisR1S5ClaimScalarEmbeddedProductSum
