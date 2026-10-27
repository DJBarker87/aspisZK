import FJo_WriterAlpha0
import FJo_ReaderAlpha0
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_AlphaPersistence
open Aeneas Aeneas.Std Result AspisR1Stage2 MultiproofConeCanonical
open OraclePortCkptAbi4Decode
/-- Actual alpha0 transport across the SAME checkpoint bytes. -/
theorem value (reserved : Bool) {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (p0 p1 : verifier.Prepared) (a0 a1 : verifier.Accumulator)
    (checkpoint proof0 pub0 proof1 pub1 : Slice U8) (hash : Hash) (saved : alloc.vec.Vec U8)
    (alpha0 alpha1 : Stage2Finish.E)
    (r0 : Array.index_usize p0.alpha 0#usize=ok alpha0) (r1 : Array.index_usize p1.alpha 0#usize=ok alpha1)
    (canonical : CanonicalWide (CheckpointBytes3Namespaces.toE alpha0))
    (write : Port3_CheckpointInstall.writer D p0 a0 proof0 pub0 hash=ok saved)
    (same : bytesOf checkpoint.val=bytesOf saved.val)
    (read : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) (VTop_Checkpoint.digest D)
      checkpoint proof1 pub1 .S2 hash=ok (.Ok (p1,a1))) :
    CheckpointBytes5Output.ofE alpha1=CheckpointBytes5Output.ofE alpha0 := by
  have writer := FJo_WriterAlpha0.value D p0 a0 proof0 pub0 hash saved alpha0 r0 canonical write
  have reader := FJo_ReaderAlpha0.value reserved (VTop_Checkpoint.digest D) checkpoint proof1 pub1 hash p1 a1 read alpha1 r1
  rw [same,writer] at reader
  have round : FoldedLeafCodec.decodeWide (OraclePortCheckpointAbiC5.encodeE (CheckpointBytes5Output.ofE alpha0))=
      some (CheckpointBytes5Output.ofE alpha0) := FoldedLeafCodec.decodeWide_encode _
  exact Option.some.inj (reader.symm.trans round)
#print axioms value
end AspisR1.FJo_AlphaPersistence
end
