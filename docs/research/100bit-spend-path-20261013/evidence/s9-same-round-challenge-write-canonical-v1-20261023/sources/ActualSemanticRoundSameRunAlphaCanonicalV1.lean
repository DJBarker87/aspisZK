import ActualSemanticRoundSourceModelV1
import ActualSemanticRoundSourceOwnerLinkV1
import ActualSemanticValidatedSamplerCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ActualSemanticRoundSameRunAlphaCanonicalV1

open AspisR1ActualSemanticRoundSourceModelV1

theorem semantic_round_success_alpha_canonical
    {H : Type} (B : Hooks)
    (D : AspisR1ActualSemanticRoundCutV1.aspis_core.digest.Digest32 H)
    (pref : AspisR1ActualSemanticRoundCutV1.r1_wire.Prefix)
    (transcript after : AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
    (alpha afterAlpha : Array QM 10#usize) (running out : QM)
    (round : Usize)
    (h : AspisR1ActualSemanticRoundSourceOwnerLinkV1.emittedRound B D pref transcript alpha running round =
      .ok (.Ok (out, afterAlpha, after))) :
    ∃ row record q,
      sourceRow round = .ok row ∧
      AspisR1ActualSemanticRoundCutV1.r1_wire.Prefix.validated_record pref row =
        .ok (.Ok record) ∧
      AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript.semantic_validated
        D transcript record = .ok (.Ok q, after) ∧
      afterAlpha = alpha.set round q ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q))) := by
  have hmodel : semanticRound B D pref transcript alpha running round =
      .ok (.Ok (out, afterAlpha, after)) := by
    rw [AspisR1ActualSemanticRoundSourceOwnerLinkV1.source_model_eq_parameterized_emission]
    exact h
  obtain ⟨row, record, q, hrow, hrecord, hsemantic, halpha⟩ :=
    semantic_round_success_slots B D pref transcript after alpha afterAlpha
      running out round hmodel
  refine ⟨row, record, q, hrow, hrecord, hsemantic, halpha, ?_⟩
  exact AspisR1ActualSemanticValidatedSamplerCanonicalV1.actual_semantic_validated_success_canonical
    D transcript after record q hsemantic

#print axioms semantic_round_success_alpha_canonical
end AspisR1ActualSemanticRoundSameRunAlphaCanonicalV1
