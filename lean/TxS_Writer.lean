import F3N_WriterReturned
import WAdm_Inventory
import WAdm_SourceWriter
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_Writer
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes3Namespaces
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical

/-- Physical encoding on the original source carriers. No chosen model Context. -/
theorem saved {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest D) hash H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8)
    (saved : alloc.vec.Vec U8) (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,(p.queries.val[j.val]'(by have h : p.queries.val.length=22 := p.queries.property; omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (Port3_DecodeCoherence.inventory p a size qb))
    (next : a.next.val=10)
    (success : Port3_CheckpointInstall.writer D p a proof pub hash=ok saved) :
    saved=Tx2N_Reader.writer H (bytesOf proof.val) (bytesOf pub.val)
      (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory p a size qb) canonical)
      (CheckpointBytes5Output.accumulator a) := by
  have erased := F3N_WriterReturned.erased D hash p a proof pub saved success
  obtain ⟨after,ran⟩ := F3N_CheckpointRun.exists_run (VTop_Checkpoint.digest D) hash _
    (alloc.vec.Vec.deref saved) [] erased
  have encoding := (CheckpointBytes5Writer.writer_effects (VTop_Checkpoint.digest D) hash H oracle
    (toPrepared p) (toAccumulator a) proof pub (alloc.vec.Vec.deref saved)
    (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb canonical next [] after ran).1
  change bytesOf saved.val = OraclePortCheckpointAbiC5.encode H (bytesOf proof.val) (bytesOf pub.val)
    (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory p a size qb) canonical)
    (CheckpointBytesBlocks.accumulator (Port3_DecodeCoherence.inventory p a size qb) canonical) at encoding
  rw [Port3_DecodeCoherence.accumulator_coherent p a size qb canonical next] at encoding
  apply Subtype.ext
  have mapped := congrArg (List.map CheckpointBytes5Writer.u8) encoding
  rw [WAdm_SourceWriter.map_bytes] at mapped
  exact mapped

#print axioms saved
end AspisR1.TxS_Writer
end
