import ActualEmittedRoundsConstructorAlphaContractV1
import S9ConstructorV3FactorsCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9EmittedRoundsConstructorFactorsV1
theorem emitted_rounds_constructor_factors_points_canonical {H : Type}
    (B : AspisR1ActualSemanticRoundSourceModelV1.Hooks)
    (zeroResult : Result AspisR1ActualSemanticRoundCutV1.aspis_core.field.QM31)
    (D : AspisR1ActualSemanticRoundCutV1.aspis_core.digest.Digest32 H)
    (pre : AspisR1ActualSemanticRoundCutV1.r1_wire.Prefix)
    (self after : AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
    (running : AspisR1ActualSemanticRoundCutV1.aspis_core.field.QM31)
    (alpha : Array AspisR1ActualSemanticRoundCutV1.aspis_core.field.QM31 10#usize)
    (variant : AspisR1S9ActualWeightsNewBoxNewV3.Variant)
    (z : Array AspisR1S9ActualWeightsNewBoxNewV3.circle.SecureCirclePoint 2#usize)
    (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights)
    (hrounds : AspisR1ActualSemanticRoundsEmittedCallerV1.emittedSemanticRounds
      B zeroResult D pre self = .ok (.Ok (running, alpha, after)))
    (hnew : AspisR1S9ActualWeightsNewBoxNewV3.weights_new variant
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1ActualSemanticRoundsConstructorAlphaV1.roundToWeightsQM alpha) z =
      .ok (.Ok w))
    (hz : AspisR1S9ConstructorV3PointScanBodyCanonicalV1.PointsCanonical z) :
    AspisR1S9ConstructorV3Loop2InnerCanonicalV1.FactorsCanonical w.factors ∧
    AspisR1S9ConstructorV3StatementCellCanonicalV1.StatementPointsCanonical w.points := by
  let mapped := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
    AspisR1ActualSemanticRoundsConstructorAlphaV1.roundToWeightsQM alpha
  have hraw := AspisR1ActualSemanticRoundsConstructorAlphaV1.mapped_alpha_reads_constructor_canonical
    alpha (AspisR1ActualSemanticRoundsEmittedCallerV1.emitted_success_all_alpha_reads_canonical
      B zeroResult D pre self after running alpha hrounds)
  have halpha : AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1.VectorCanonical mapped := by
    intro i q hread
    have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.toProbeQ mapped i
    change Array.index_usize
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9ConstructorV3Loop2InnerCanonicalV1.toProbeQ mapped) i = .ok q at hread
    rw [hread] at hm
    cases hr : Array.index_usize mapped i with
    | fail e => rw [hr] at hm; cases hm
    | div => rw [hr] at hm; cases hm
    | ok v =>
      rw [hr] at hm
      have he : AspisR1S9ConstructorV3Loop2InnerCanonicalV1.toProbeQ v = q := Result.ok.inj hm
      subst q
      have hv := hraw i v hr
      change ((v.c0.a.val < AspisR1.ExtractedCurrentTowerAdd.P ∧
        v.c0.b.val < AspisR1.ExtractedCurrentTowerAdd.P) ∧
        (v.c1.a.val < AspisR1.ExtractedCurrentTowerAdd.P ∧
        v.c1.b.val < AspisR1.ExtractedCurrentTowerAdd.P)) at hv ⊢
      exact hv
  exact AspisR1S9ConstructorV3FactorsCanonicalV1.constructor_success_factors_and_points_canonical
    variant mapped z w halpha hz hnew

#print axioms emitted_rounds_constructor_factors_points_canonical
end AspisR1S9EmittedRoundsConstructorFactorsV1
