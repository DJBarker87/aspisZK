import AspisR1ActualSemanticRoundCutV1.Funs
import ActualCutSemanticValidatedSamplerReadbackV1
import ActualSemanticSamplerTotalV1

set_option autoImplicit false
namespace AspisR1ActualSemanticValidatedSamplerCanonicalV1

theorem actual_semantic_validated_success_canonical
    {H : Type} (digest : AspisR1ActualSemanticRoundCutV1.aspis_core.digest.Digest32 H)
    (transcript transcript' : AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
    (record : AspisR1ActualSemanticRoundCutV1.r1_wire.ValidatedRecord)
    (q : AspisR1ActualSemanticRoundCutV1.aspis_core.field.QM31)
    (h : AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript.semantic_validated
      digest transcript record = .ok (.Ok q, transcript')) :
    AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld
          (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q))) := by
  obtain ⟨block, hsample⟩ :=
    AspisR1ActualCutSemanticValidatedSamplerReadbackV1.semantic_validated_success_has_sampler
      digest transcript transcript' record q h
  exact AspisR1ActualSemanticSamplerTotalV1.actual_sample_success_canonical
    block q hsample

#print axioms actual_semantic_validated_success_canonical
end AspisR1ActualSemanticValidatedSamplerCanonicalV1
