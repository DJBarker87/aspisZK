import S9CurrentCheckpointKDecoderReaderAcceptedV1
import S9CheckpointSemanticAlphaCanonicalV1
import S9CheckpointSemanticAlphaSourceV1
import OraclePortCkptAbiSourceFields
import S4ResumeGammaActualCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CurrentReaderCheckpointAdoptionV1
open AspisR1Stage2
open AspisR1.CheckpointBytes4Sections AspisR1.CheckpointBytes4Ops
abbrev Canonical := AspisR1S9ReaderKActualQMCanonicalV1.Canonical
abbrev currentK := AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent

/-- The exact existing ten-read operation model, now using the accepted-current
source decoder reader. No equality of rejection traces is asserted. -/
def semanticCurrent (raw : (n : Usize) → verifier.Reader → Result (Array U8 n × verifier.Reader)) :=
  semanticUsing (currentK raw)

theorem semantic_current_success_canonical
    (raw : (n : Usize) → verifier.Reader → Result (Array U8 n × verifier.Reader))
    (bytes : Slice U8) (start finish : Usize) (values : Array K 10#usize)
    (success : semanticCurrent raw bytes start=.ok (.Ok (values,finish))) :
    ∀ q ∈ values.val, Canonical q := by
  obtain ⟨last,run,_⟩ := AspisR1.CheckpointBytes4SemanticFields.semantic_fields
    (currentK raw) bytes start finish values success
  exact AspisR1S9CheckpointSemanticAlphaCanonicalV1.read_list_canonical (currentK raw) Canonical
    (AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent_success_canonical raw)
    10 ⟨bytes,start⟩ last values.val run

theorem semantic_current_reads_canonical
    (raw : (n : Usize) → verifier.Reader → Result (Array U8 n × verifier.Reader))
    (bytes : Slice U8) (start finish : Usize) (values : Array K 10#usize)
    (success : semanticCurrent raw bytes start=.ok (.Ok (values,finish)))
    (i : Usize) (q : K) (hindex : Array.index_usize values i=.ok q) : Canonical q := by
  cases hget : values[i]? with
  | none => simp only [Array.index_usize,hget] at hindex; cases hindex
  | some value =>
    simp only [Array.index_usize,hget] at hindex
    have he : value=q := Result.ok.inj hindex
    have hget' : values.val[i.val]?=some value := by simpa using hget
    have hmem : value ∈ values.val := List.mem_of_getElem? hget'
    rw [←he]
    exact semantic_current_success_canonical raw bytes start finish values success value hmem

/-- Explicit content/source-cut installer. Actual raw reader and whole native
caller/runtime/ABI adoption remain separate source boundaries. -/
def withCurrentCheckpointReaders (ops : ResumeOps) : ResumeOps :=
  {AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops with
    readK := currentK ops.raw
    readSemanticAlpha := AspisR1S9CheckpointSemanticAlphaSourceV1.source (currentK ops.raw)}

theorem same_fields_semantic_current_canonical
    (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (fields : AspisR1.OraclePortCkptAbiSourceFields.Fields (withCurrentCheckpointReaders ops) bytes v p acc)
    (i : Usize) (q : K) (hindex : Array.index_usize p.semantic_alpha i=.ok q) : Canonical q := by
  have hsemantic := fields.semanticRead
  change AspisR1S9CheckpointSemanticAlphaSourceV1.source (currentK ops.raw)
    bytes fields.rQueries.at=.ok (.Ok (p.semantic_alpha,fields.semanticEnd)) at hsemantic
  rw [AspisR1S9CheckpointSemanticAlphaSourceV1.source_eq_semanticUsing] at hsemantic
  exact semantic_current_reads_canonical ops.raw bytes fields.rQueries.at fields.semanticEnd
    p.semantic_alpha hsemantic i q hindex

/-- SAME accepted resume supplies all four circle coordinates and the semantic
alpha array from the actual-current decoder reader and exact source ten-read
helper. No old-reader execution equality or child success premise is needed. -/
theorem resume_current_checkpoint_inputs_canonical
    (ops : ResumeOps) {H : Type} (D : aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (success : verifier.resumeWithOps (withCurrentCheckpointReaders ops) D bytes proof publicInput v hash=
      .ok (.Ok (p,acc))) :
    (∃ x0 y0 x1 y1 : K,
      p.z=Array.make 2#usize [⟨x0,y0⟩,⟨x1,y1⟩] ∧
      Canonical x0 ∧ Canonical y0 ∧ Canonical x1 ∧ Canonical y1) ∧
    (∀ (i : Usize) (q : K), Array.index_usize p.semantic_alpha i=.ok q → Canonical q) := by
  obtain ⟨fields⟩ := AspisR1.OraclePortCkptAbiSourceFields.successful_fields
    (withCurrentCheckpointReaders ops) D bytes proof publicInput v hash p acc success
  constructor
  · refine ⟨fields.x0,fields.y0,fields.x1,fields.y1,fields.coordinates,?_,?_,?_,?_⟩
    · exact AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent_success_canonical ops.raw _ _ _ fields.x0Read
    · exact AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent_success_canonical ops.raw _ _ _ fields.y0Read
    · exact AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent_success_canonical ops.raw _ _ _ fields.x1Read
    · exact AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent_success_canonical ops.raw _ _ _ fields.y1Read
  · intro i q hindex
    exact same_fields_semantic_current_canonical ops bytes v p acc fields i q hindex

#print axioms semantic_current_success_canonical
#print axioms semantic_current_reads_canonical
#print axioms same_fields_semantic_current_canonical
#print axioms resume_current_checkpoint_inputs_canonical
end AspisR1S9CurrentReaderCheckpointAdoptionV1
