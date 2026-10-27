import FJo_BodyGamma
import SdkD_WriterRoots
import F3L_WriterNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_WriterGamma
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft MultiproofConeCanonical
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec
/-- Literal gamma bytes in THIS writer return. -/
theorem value {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (proof pub : Slice U8) (hash : Hash) (saved : alloc.vec.Vec U8)
    (canonical : CanonicalWide (CheckpointBytes3Namespaces.toE p.gamma))
    (run : Port3_CheckpointInstall.writer D p a proof pub hash=ok saved) :
    slice (bytesOf saved.val) 176 32=OraclePortCheckpointAbiC5.encodeE (CheckpointBytes5Output.ofE p.gamma) := by
  obtain ⟨hp,hu,hc,source⟩ := SdkD_WriterSource.returned D p a proof pub hash saved run
  have encoded := congrArg bytesOf source
  rw [CheckpointBytes5Writer.finish_bytes] at encoded
  rw [encoded]
  have bodyLength : (CheckpointBytesDecodeC5.sourceBody (CheckpointBytes3Namespaces.toPrepared p)
      (CheckpointBytes3Namespaces.toAccumulator a) hp hu).length=1736 := by
    simp only [CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]
  rw [SdkD_WriterRoots.slice_append _ _ 176 32 (by rw [bodyLength];decide),
    FJo_BodyGamma.value _ _ _ _ canonical,F3L_WriterNumeric.exact_e,
    CheckpointBytes3Namespaces.from_to_e]
#print axioms value
end AspisR1.FJo_WriterGamma
end
