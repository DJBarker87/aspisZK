import FJo_WriterGamma
import FJo_ReaderGamma
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_GammaPersistence
open Aeneas Aeneas.Std Result AspisR1Stage2
open MultiproofConeCanonical
open OraclePortCkptAbi4Decode
/-- Writer/reader scalar transport through the identical literal checkpoint bytes. -/
theorem value (reserved : Bool) {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (p0 p1 : verifier.Prepared) (a0 a1 : verifier.Accumulator)
    (checkpoint proof0 pub0 proof1 pub1 : Slice U8) (hash : Hash) (saved : alloc.vec.Vec U8)
    (canonical : CanonicalWide (CheckpointBytes3Namespaces.toE p0.gamma))
    (write : Port3_CheckpointInstall.writer D p0 a0 proof0 pub0 hash=ok saved)
    (same : bytesOf checkpoint.val=bytesOf saved.val)
    (read : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) (VTop_Checkpoint.digest D)
      checkpoint proof1 pub1 .S2 hash=ok (.Ok (p1,a1))) :
    CheckpointBytes5Output.ofE p1.gamma=CheckpointBytes5Output.ofE p0.gamma := by
  have writer := FJo_WriterGamma.value D p0 a0 proof0 pub0 hash saved canonical write
  have reader := FJo_ReaderGamma.value reserved (VTop_Checkpoint.digest D) checkpoint proof1 pub1 hash p1 a1 read
  rw [same,writer,FoldedLeafCodec.decodeWide_encode] at reader
  exact (Option.some.inj reader).symm
#print axioms value
end AspisR1.FJo_GammaPersistence
end
