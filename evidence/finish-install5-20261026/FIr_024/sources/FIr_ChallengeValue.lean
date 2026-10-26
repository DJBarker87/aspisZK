import FIq_TypedData
import F3L_RhoMeaning
import S1OriginalNewStaticFieldsV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_ChallengeValue
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation

/-- Both interpretations copy the same four M31 limbs into the same tower. -/
theorem decode_value (q : aspis_core.field.QM31) :
    algebraMap ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact
      (RawActualAnnotatedPolynomialRun.DecodeMain q)=
    LiteralOpeningView.eK (F3L_RhoMeaning.decode q) := by
  rfl

/-- Static semantic-alpha equality survives the current/retained carrier map. -/
theorem alpha_same (out : verifier.Prepared)
    (alpha : Array AspisR1CurrentCaller.aspis_core.field.QM31 10#usize)
    (same : (currentPrepared out).semantic_alpha=alpha) :
    out.semantic_alpha=AspisR1ClaimPreparedBridge.mapArray retainedQ alpha := by
  have mapped := congrArg (AspisR1ClaimPreparedBridge.mapArray retainedQ) same
  change AspisR1ClaimPreparedBridge.mapArray retainedQ
    (AspisR1ClaimPreparedBridge.mapArray currentQ out.semantic_alpha)=_ at mapped
  have back : AspisR1ClaimPreparedBridge.mapArray retainedQ
      (AspisR1ClaimPreparedBridge.mapArray currentQ out.semantic_alpha)=out.semantic_alpha := by
    apply Subtype.ext
    simp only [AspisR1ClaimPreparedBridge.mapArray,List.map_map]
    congr 1
  rw [back] at mapped
  exact mapped

#print axioms decode_value
#print axioms alpha_same
end AspisR1.FIr_ChallengeValue
end
