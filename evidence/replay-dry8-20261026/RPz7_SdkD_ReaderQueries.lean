import RPz7_SdkD_ReaderRoots
import RPz7_SdkD_WriterQueries
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_ReaderQueries
open Aeneas Aeneas.Std Result AspisR1Stage2
open MultiproofConeCanonical OraclePortCompactDraft

theorem returned (reserved : Bool) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (checkpoint proof pub : Slice U8) (hash : Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) D checkpoint proof pub .S2 hash =
      ok (.Ok (p,a))) :
    ∀ j : Fin 22, little (slice (bytesOf checkpoint.val) (320+4*j.val) 4) =
      (p.queries.val[j.val]'(by simpa using j.isLt)).val := by
  obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D checkpoint proof pub .S2 hash p a success
  obtain ⟨_,_,_,_,_,length,_⟩ := Tx2N_Header.cuts reserved D checkpoint proof pub hash p a success
  have flat := CheckpointBytes4Layout.flat_fields reserved checkpoint p a f length
  have values := CheckpointBytes4QueryDecode.query_values reserved f.rRho f.rQueries p.queries.val
    f.queriesRead (by
      rw [flat.rhoCursor,flat.rhoBacking]
      have queryLength : p.queries.val.length = 22 := p.queries.property
      rw [queryLength,length]; decide)
  intro j
  have value := values ⟨j.val,by simpa using j.isLt⟩
  simpa only [flat.rhoCursor,flat.rhoBacking,Nat.mul_comm] using value

theorem writer_reader (reserved : Bool) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (p0 p1 : verifier.Prepared) (a0 a1 : verifier.Accumulator)
    (checkpoint proof pub : Slice U8) (hash : Hash) (saved : alloc.vec.Vec U8)
    (write : Port3_CheckpointInstall.writer D p0 a0 proof pub hash = ok saved)
    (same : bytesOf checkpoint.val = bytesOf saved.val)
    (read : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) (VTop_Checkpoint.digest D)
      checkpoint proof pub .S2 hash = ok (.Ok (p1,a1))) : p1.queries = p0.queries := by
  have writer := SdkD_WriterQueries.returned D p0 a0 proof pub hash saved write
  have reader := returned reserved (VTop_Checkpoint.digest D) checkpoint proof pub hash p1 a1 read
  apply Subtype.ext
  apply List.ext_getElem
  · rw [p1.queries.property,p0.queries.property]
  · intro i hi hj
    have bound : i < 22 := by simpa using hi
    have result := reader ⟨i,bound⟩
    rw [same,writer ⟨i,bound⟩,OraclePortCheckpointPreparedC5.little_le32 _ (by scalar_tac)] at result
    exact UScalar.eq_of_val_eq result.symm

#print axioms returned
#print axioms writer_reader
end AspisR1.SdkD_ReaderQueries
end
