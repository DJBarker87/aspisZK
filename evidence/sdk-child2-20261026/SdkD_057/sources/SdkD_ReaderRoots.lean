import SdkD_WriterRoots
import Tx2N_Header
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_ReaderRoots
open Aeneas Aeneas.Std Result AspisR1Stage2
open MultiproofConeCanonical OraclePortCompactDraft

theorem returned (reserved : Bool) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (checkpoint proof pub : Slice U8) (hash : Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) D checkpoint proof pub .S2 hash =
      ok (.Ok (p,a))) :
    bytesOf (Port3_BatchStage.root0 p).val = slice (bytesOf checkpoint.val) 112 32 ∧
    bytesOf (Port3_BatchStage.root1 p).val = slice (bytesOf checkpoint.val) 144 32 := by
  obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D checkpoint proof pub .S2 hash p a success
  obtain ⟨_,_,_,_,_,length,_⟩ := Tx2N_Header.cuts reserved D checkpoint proof pub hash p a success
  have flat := CheckpointBytes4Layout.flat_fields reserved checkpoint p a f length
  have first := congrArg bytesOf flat.root0Bytes
  have second := congrArg bytesOf flat.root1Bytes
  simp only [bytesOf,List.map_take,List.map_drop] at first second
  simpa only [Port3_BatchStage.root0,Port3_BatchStage.root1,f.roots,Array.make,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,slice] using And.intro first second

/-- The raw roots survive the actual writer/reader pair. No canonical
arithmetic, authenticated opening map or ten-step model equation is assumed. -/
theorem writer_reader (reserved : Bool) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (p0 p1 : verifier.Prepared) (a0 a1 : verifier.Accumulator)
    (checkpoint proof pub : Slice U8) (hash : Hash) (saved : alloc.vec.Vec U8)
    (write : Port3_CheckpointInstall.writer D p0 a0 proof pub hash = ok saved)
    (same : bytesOf checkpoint.val = bytesOf saved.val)
    (read : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) (VTop_Checkpoint.digest D)
      checkpoint proof pub .S2 hash = ok (.Ok (p1,a1))) :
    Port3_BatchStage.root0 p1 = Port3_BatchStage.root0 p0 ∧
    Port3_BatchStage.root1 p1 = Port3_BatchStage.root1 p0 := by
  have writer := SdkD_WriterRoots.returned D p0 a0 proof pub hash saved write
  have reader := returned reserved (VTop_Checkpoint.digest D) checkpoint proof pub hash p1 a1 read
  rw [same,writer.1,writer.2] at reader
  exact ⟨Subtype.ext (MultiproofConeByteEquality.bytes_injective reader.1),
    Subtype.ext (MultiproofConeByteEquality.bytes_injective reader.2)⟩

#print axioms returned
#print axioms writer_reader
end AspisR1.SdkD_ReaderRoots
end
