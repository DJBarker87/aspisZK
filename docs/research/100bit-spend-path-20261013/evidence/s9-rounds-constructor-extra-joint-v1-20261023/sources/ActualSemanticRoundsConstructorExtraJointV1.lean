import ActualSemanticRoundsConstructorAlphaContractV1
import S9ActualWeightsNewExtraCurrentCanonicalV3
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1ActualSemanticRoundsConstructorExtraJointV1

abbrev RoundQM := AspisR1ActualSemanticRoundCutV1.aspis_core.field.QM31
abbrev ConstructorQM := AspisR1S9ActualWeightsNewBoxNewV3.field.QM31
abbrev ConstructorWeights := AspisR1S9ActualWeightsNewBoxNewV3.Weights

/-- Compose the actual-source-shaped ten-round alpha canonicality theorem with
 the same successful extracted constructor call. This closes only the
 Actual-only semantic-round model to the constructor's extra-array proof; the
 Hooks-to-Rust caller refinement remains an independent boundary. -/
theorem actual_rounds_constructor_extra_success_canonical {H : Type}
    (B : AspisR1ActualSemanticRoundSourceModelV1.Hooks)
    (D : AspisR1ActualSemanticRoundCutV1.aspis_core.digest.Digest32 H)
    (pre : AspisR1ActualSemanticRoundCutV1.r1_wire.Prefix)
    (self after : AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
    (running : RoundQM) (alpha : Array RoundQM 10#usize)
    (variant : AspisR1S9ActualWeightsNewBoxNewV3.Variant)
    (z : Array AspisR1S9ActualWeightsNewBoxNewV3.circle.SecureCirclePoint 2#usize)
    (w : ConstructorWeights)
    (hrounds : AspisR1ActualSemanticRoundsCanonicalV1.actualSourceRounds
      B D pre self = .ok (.Ok (running, alpha, after)))
    (hnew : AspisR1S9ActualWeightsNewBoxNewV3.weights_new variant
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1ActualSemanticRoundsConstructorAlphaV1.roundToWeightsQM alpha) z =
        .ok (.Ok w)) :
    ∃ q8 q9,
      Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1ActualSemanticRoundsConstructorAlphaV1.roundToWeightsQM alpha)
        8#usize = .ok q8 ∧
      Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1ActualSemanticRoundsConstructorAlphaV1.roundToWeightsQM alpha)
        9#usize = .ok q9 ∧
      w.extra = Array.make 2#usize [q8, q9] ∧
      ∀ (j : Usize) (v : AspisR1CurrentWide.field.QM31),
        Array.index_usize
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
            AspisR1S9ActualWeightsNewExtraCurrentCanonicalV3.candidateToCurrentQM w.extra)
          j = .ok v → AspisR1CurrentWide.Proof.CanonicalQM v := by
  have halpha :=
    AspisR1ActualSemanticRoundsConstructorAlphaContractV1.actual_rounds_success_constructor_alpha_contract
      B D pre self after running alpha hrounds
  exact AspisR1S9ActualWeightsNewExtraCurrentCanonicalV3.weights_new_extra_current_fullread_canonical_v3
    variant
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1ActualSemanticRoundsConstructorAlphaV1.roundToWeightsQM alpha)
    z w hnew halpha

#print axioms actual_rounds_constructor_extra_success_canonical
end AspisR1ActualSemanticRoundsConstructorExtraJointV1
