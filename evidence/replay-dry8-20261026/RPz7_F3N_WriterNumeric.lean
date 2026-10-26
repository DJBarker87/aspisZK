import RPz7_F3N_WriterReturned
import RPz7_F3L_WriterBody
import RPz7_WAdm_SourceWriter
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_WriterNumeric
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes3Namespaces
open F3K_CheckpointPreparedFields MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem saved {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest D) hash H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (a : verifier.Accumulator)
    (proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22:=(writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out)
      (toAccumulator a) (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb))
    (next : a.next.val=10)
    (success : Port3_CheckpointInstall.writer D
      (Tx1Q_Carriers.prepared (AspisR1CurrentCaller.InstalledPreparation.currentPrepared out)) a proof pub hash=ok saved) :
    saved=Tx2N_Reader.writer H (bytesOf proof.val) (bytesOf pub.val)
      (F3L_SourcePrepared.numeric out) (CheckpointBytes5Output.accumulator a) := by
  have erased := F3N_WriterReturned.erased D hash _ a proof pub saved success
  obtain ⟨after,ran⟩ := F3N_CheckpointRun.exists_run (VTop_Checkpoint.digest D) hash _
    (alloc.vec.Vec.deref saved) [] erased
  have encoding := (CheckpointBytes5Writer.writer_effects (VTop_Checkpoint.digest D) hash H oracle
    (writerPrepared out) (toAccumulator a) proof pub (alloc.vec.Vec.deref saved)
    (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb canonical next [] after ran).1
  rw [F3L_WriterPreparedEq.numeric,F3L_WriterAccumulator.numeric _ a size qb canonical next] at encoding
  apply Subtype.ext
  have mapped := congrArg (List.map CheckpointBytes5Writer.u8) encoding
  rw [WAdm_SourceWriter.map_bytes] at mapped
  exact mapped

#print axioms saved
end AspisR1.F3N_WriterNumeric
end
