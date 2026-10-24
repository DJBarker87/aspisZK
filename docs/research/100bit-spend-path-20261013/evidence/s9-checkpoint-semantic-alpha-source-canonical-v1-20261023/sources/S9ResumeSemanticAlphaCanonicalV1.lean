import S9CheckpointSemanticAlphaCanonicalV1
import OraclePortCkptAbiSourceFields
import S9CheckpointSemanticAlphaSourceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ResumeSemanticAlphaCanonicalV1
open AspisR1Stage2

/-- Install the exact generated ten-read helper operation cut with the concrete strict 16-byte QM
reader. This is an explicit content-model installer, not an assertion that all
remaining native callbacks have been refined. -/
def withSemanticAlpha (ops : ResumeOps) : ResumeOps :=
  {ops with readSemanticAlpha := (AspisR1S9CheckpointSemanticAlphaSourceV1.source (AspisR1S9ReaderKActualQMCanonicalV1.readerK ops.raw))}

theorem same_resume_fields_semantic_alpha_canonical
    (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (fields : AspisR1.OraclePortCkptAbiSourceFields.Fields (withSemanticAlpha ops) bytes v p acc)
    (i : Usize) (q : aspis_core.field.QM31)
    (hindex : Array.index_usize p.semantic_alpha i = .ok q) :
    AspisR1S9ReaderKActualQMCanonicalV1.Canonical q := by
  have hsemantic := fields.semanticRead
  change AspisR1S9CheckpointSemanticAlphaSourceV1.source
    (AspisR1S9ReaderKActualQMCanonicalV1.readerK ops.raw) bytes fields.rQueries.at =
      .ok (.Ok (p.semantic_alpha,fields.semanticEnd)) at hsemantic
  rw [AspisR1S9CheckpointSemanticAlphaSourceV1.source_eq_semanticUsing] at hsemantic
  exact AspisR1S9CheckpointSemanticAlphaCanonicalV1.semantic_alpha_reads_canonical
    ops.raw bytes fields.rQueries.at fields.semanticEnd p.semantic_alpha hsemantic i q hindex

/-- Accepted resume success itself supplies the exact semantic-alpha helper
call and array output; there is no separately supplied successful child call. -/
theorem successful_resume_semantic_alpha_canonical
    (ops : ResumeOps) {H : Type} (digest : aspis_core.digest.Digest32 H)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (success : verifier.resumeWithOps (withSemanticAlpha ops) digest bytes proof public1 v hash =
      .ok (.Ok (p,acc)))
    (i : Usize) (q : aspis_core.field.QM31)
    (hindex : Array.index_usize p.semantic_alpha i = .ok q) :
    AspisR1S9ReaderKActualQMCanonicalV1.Canonical q := by
  obtain ⟨fields⟩ := AspisR1.OraclePortCkptAbiSourceFields.successful_fields
    (withSemanticAlpha ops) digest bytes proof public1 v hash p acc success
  exact same_resume_fields_semantic_alpha_canonical ops bytes v p acc fields i q hindex

#print axioms same_resume_fields_semantic_alpha_canonical
#print axioms successful_resume_semantic_alpha_canonical
end AspisR1S9ResumeSemanticAlphaCanonicalV1
