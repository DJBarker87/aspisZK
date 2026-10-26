import TxS_Transfer
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_Reader
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes3Namespaces
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCheckpointAbiC5

theorem saved (base : VTop_Stages.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (checkpoint proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (source target : verifier.Prepared) (old fresh : verifier.Accumulator)
    (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest D) hash H)
    (originalProof originalPub : Slice U8)
    (size : old.weights.val.length=64)
    (qb : ∀ j : Fin 22,(source.queries.val[j.val]'(by have h : source.queries.val.length=22:=source.queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (Port3_DecodeCoherence.inventory source old size qb))
    (next : old.next.val=10)
    (written : Port3_CheckpointInstall.writer D source old originalProof originalPub hash=ok saved)
    (same : bytesOf checkpoint.val=bytesOf saved.val)
    (read : (Tx2N_Install.inner base reserved query).op18 D checkpoint proof pub .S2 hash=ok (.Ok (target,fresh))) :
    CheckpointBytes4SavedFields.BodyMatches target fresh
      (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory source old size qb) canonical)
      (CheckpointBytes5Output.accumulator old) ∧
    CheckpointBytes5Output.accumulator fresh=CheckpointBytes5Output.accumulator old := by
  have encoded := TxS_Writer.saved D hash H oracle source old originalProof originalPub saved size qb canonical next written
  have encoding : bytesOf checkpoint.val=OraclePortCheckpointAbiC5.encode H
      (bytesOf originalProof.val) (bytesOf originalPub.val)
      (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory source old size qb) canonical)
      (CheckpointBytes5Output.accumulator old) := by
    rw [same,encoded,Tx2N_Reader.writer_bytes]
  have success := Tx2N_Install.reader_success base reserved query D hash checkpoint proof pub .S2 target fresh read
  obtain ⟨fields,cursor,allocation⟩ := CheckpointBytes4SuccessfulFields.successful_saved_fields
    reserved (VTop_Checkpoint.digest D) checkpoint proof pub hash target fresh H
    (bytesOf originalProof.val) (bytesOf originalPub.val) _ _ encoding next success
  exact ⟨fields,(CheckpointBytes5Output.fields_observation target fresh _ _ fields cursor).2.2⟩

#print axioms saved
end AspisR1.TxS_Reader
end
