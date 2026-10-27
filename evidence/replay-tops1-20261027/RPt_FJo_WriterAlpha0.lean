import RPt_FJo_BodyAlpha0
import RPt_FJo_AlphaIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_WriterAlpha0
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCompactDraft MultiproofConeCanonical
open OraclePortCkptAbi4Decode
/-- Literal alpha0 bytes in THIS writer return. -/
theorem value {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof pub : Slice U8) (hash : Hash) (saved : alloc.vec.Vec U8)
    (alpha : aspis_core.field.wide_exact.WideExact) (read : Array.index_usize p.alpha 0#usize=ok alpha)
    (canonical : CanonicalWide (CheckpointBytes3Namespaces.toE alpha))
    (run : Port3_CheckpointInstall.writer D p a proof pub hash=ok saved) :
    slice (bytesOf saved.val) 240 32=OraclePortCheckpointAbiC5.encodeE (CheckpointBytes5Output.ofE alpha) := by
  obtain ⟨hp,hu,hc,source⟩ := SdkD_WriterSource.returned D p a proof pub hash saved run
  have encoded := congrArg bytesOf source
  rw [CheckpointBytes5Writer.finish_bytes] at encoded
  rw [encoded]
  have bodyLength : (CheckpointBytesDecodeC5.sourceBody (CheckpointBytes3Namespaces.toPrepared p)
      (CheckpointBytes3Namespaces.toAccumulator a) hp hu).length=1736 := by
    simp only [CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]
  have index := FJo_AlphaIndex.value p alpha read
  rw [SdkD_WriterRoots.slice_append _ _ 240 32 (by rw [bodyLength];decide)]
  rw [FJo_BodyAlpha0.value _ _ _ _ (by rwa [index]),F3L_WriterNumeric.exact_e]
  rw [index,CheckpointBytes3Namespaces.from_to_e]
#print axioms value
end AspisR1.FJo_WriterAlpha0
end
