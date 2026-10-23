import AspisR1ActualSemanticRoundCutV1.Funs
import ActualSamplerDigitWholeMapV1
import ExtractedDigest32SamplerTransport

set_option autoImplicit false
namespace AspisR1ActualSemanticSamplerTotalV1
open Aeneas Aeneas.Std Result

theorem actual_sample_success_canonical (block : Array U8 32#usize)
    (q : AspisR1ActualSemanticRoundCutV1.aspis_core.field.QM31)
    (hsample_actual : AspisR1ActualSemanticRoundCutV1.sampler.qm31_sample block = .ok q) :
    AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld
          (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q))) := by
  obtain ⟨q0, hsample, hcanonical, _hcoordinates⟩ :=
    AspisR1PublicPreparation.SamplerTransport.sample_total block
  have hmap := AspisR1ActualSamplerDigitWholeMapV1.sample_result_map block
  rw [hsample_actual] at hmap
  simp only [bind_tc_ok] at hmap
  have heq : AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q = q0 :=
    Result.ok.inj (hmap.trans hsample)
  exact heq.symm ▸ hcanonical

#print axioms actual_sample_success_canonical
end AspisR1ActualSemanticSamplerTotalV1
