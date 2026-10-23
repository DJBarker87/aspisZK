import ActualEmittedRoundsConstructorAlphaContractV1
import S9ConstructorHelperJointV3

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1ActualEmittedRoundsConstructorHelperJointV1
open AspisR1S9PairTwoBodyCanonicalStatesV1
open AspisR1S9ConstructorPairExtraContractV3

/-- Compose success of the actual parameterized emitted ten-round caller with
its mapped-alpha constructor execution and the same helper execution. The
constructor's independent alpha canonicality premise is discharged. Hooks,
source/runtime correspondence, ap0/ap1 producer contracts and the complete
Pair caller remain explicit external boundaries. -/
theorem emitted_rounds_constructor_helper_output_canonical {H : Type}
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
    (ap0 ap1 output : PairArray)
    (hrounds : AspisR1ActualSemanticRoundsEmittedCallerV1.emittedSemanticRounds
      B zeroResult D pre self = .ok (.Ok (running, alpha, after)))
    (hnew : AspisR1S9ActualWeightsNewBoxNewV3.weights_new variant
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1ActualSemanticRoundsConstructorAlphaV1.roundToWeightsQM alpha) z =
      .ok (.Ok w))
    (hhelper : AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights
      ap0 ap1 (pairExtra w) = .ok output)
    (hap0 : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW ap0)) j = .ok v → Canonical v)
    (hap1 : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW ap1)) j = .ok v →
        AspisR1S9HighTermsTraceV1.canonicalW v) :
    ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW output)) j = .ok v →
      Canonical v := by
  have halpha :=
    AspisR1ActualEmittedRoundsConstructorAlphaContractV1.emitted_rounds_success_constructor_alpha_contract
      B zeroResult D pre self after running alpha hrounds
  exact AspisR1S9ConstructorHelperJointV3.constructor_helper_output_canonical
    variant
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
      AspisR1ActualSemanticRoundsConstructorAlphaV1.roundToWeightsQM alpha)
    z w ap0 ap1 output hnew halpha hhelper hap0 hap1

#print axioms emitted_rounds_constructor_helper_output_canonical
end AspisR1ActualEmittedRoundsConstructorHelperJointV1
