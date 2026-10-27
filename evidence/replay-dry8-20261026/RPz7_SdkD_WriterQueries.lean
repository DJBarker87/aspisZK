import RPz7_SdkD_WriterQueryCells
import RPz7_SdkD_WriterRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_WriterQueries
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical OraclePortCompactDraft

theorem returned {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (proof pub : Slice U8) (hash : Hash) (saved : alloc.vec.Vec U8)
    (success : Port3_CheckpointInstall.writer D p a proof pub hash = ok saved) :
    ∀ j : Fin 22, slice (bytesOf saved.val) (320+4*j.val) 4 =
      le32 (p.queries.val[j.val]'(by simpa using j.isLt)).val := by
  obtain ⟨hp,hu,hc,source⟩ := SdkD_WriterSource.returned D p a proof pub hash saved success
  have encoded := congrArg bytesOf source
  rw [CheckpointBytes5Writer.finish_bytes] at encoded
  intro j
  rw [encoded,SdkD_WriterRoots.slice_append _ _ (320+4*j.val) 4 (by
    simp only [CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]
    have := j.isLt; omega),SdkD_WriterQueryCells.query]
  rfl

theorem length {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (proof pub : Slice U8) (hash : Hash) (saved : alloc.vec.Vec U8)
    (success : Port3_CheckpointInstall.writer D p a proof pub hash = ok saved) :
    saved.val.length = 1768 := by
  obtain ⟨hp,hu,hc,source⟩ := SdkD_WriterSource.returned D p a proof pub hash saved success
  rw [source]
  simp only [CheckpointBytes5Writer.finish,List.length_append,List.length_map,
    CheckpointBytesDecodeC5.sourceBody,List.length_ofFn,hc.property]
  rfl

#print axioms returned
#print axioms length
end AspisR1.SdkD_WriterQueries
end
