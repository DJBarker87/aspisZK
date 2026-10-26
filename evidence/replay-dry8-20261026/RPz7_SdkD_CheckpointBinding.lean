import RPz7_SdkD_ReaderQueries
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_CheckpointBinding
open Aeneas Aeneas.Std Result AspisR1Stage2
open MultiproofConeCanonical OraclePortCompactDraft

/-- Root/query transport needs the SAME checkpoint bytes; proof/public bytes
are each call's actual arguments and need not be definitionally identical. -/
theorem fields (reserved : Bool) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (p0 p1 : verifier.Prepared) (a0 a1 : verifier.Accumulator)
    (checkpoint proof0 pub0 proof1 pub1 : Slice U8) (hash : Hash) (saved : alloc.vec.Vec U8)
    (write : Port3_CheckpointInstall.writer D p0 a0 proof0 pub0 hash = ok saved)
    (same : bytesOf checkpoint.val = bytesOf saved.val)
    (read : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) (VTop_Checkpoint.digest D)
      checkpoint proof1 pub1 .S2 hash = ok (.Ok (p1,a1))) :
    Port3_BatchStage.root0 p1 = Port3_BatchStage.root0 p0 ∧
    Port3_BatchStage.root1 p1 = Port3_BatchStage.root1 p0 ∧ p1.queries = p0.queries := by
  have writer := SdkD_WriterRoots.returned D p0 a0 proof0 pub0 hash saved write
  have reader := SdkD_ReaderRoots.returned reserved (VTop_Checkpoint.digest D) checkpoint proof1 pub1 hash p1 a1 read
  rw [same,writer.1,writer.2] at reader
  refine ⟨Subtype.ext (MultiproofConeByteEquality.bytes_injective reader.1),
    Subtype.ext (MultiproofConeByteEquality.bytes_injective reader.2),?_⟩
  have writerQ := SdkD_WriterQueries.returned D p0 a0 proof0 pub0 hash saved write
  have readerQ := SdkD_ReaderQueries.returned reserved (VTop_Checkpoint.digest D) checkpoint proof1 pub1 hash p1 a1 read
  apply Subtype.ext
  apply List.ext_getElem
  · rw [p1.queries.property,p0.queries.property]
  · intro i hi hj
    have bound : i < 22 := by simpa using hi
    have result := readerQ ⟨i,bound⟩
    rw [same,writerQ ⟨i,bound⟩,OraclePortCheckpointPreparedC5.little_le32 _ (by scalar_tac)] at result
    exact UScalar.eq_of_val_eq result.symm

#print axioms fields
end AspisR1.SdkD_CheckpointBinding
end
