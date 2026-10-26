import RPz7_Tx2N_Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_ReaderNumeric
open Aeneas Aeneas.Std Result AspisR1Stage2 Tx2N_Reader
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5

theorem saved_ten (base : VTop_Stages.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (checkpoint proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (H : Bytes → State) (stored publicBytes : Bytes) (pm : Prepared)
    (am : QueryAccumulator.State K E) (ten : am.next=10)
    (same : bytesOf checkpoint.val = bytesOf saved.val)
    (tx1_saved : saved = writer H stored publicBytes pm
      am)
    (success : (Tx2N_Install.inner base reserved query).op18 D checkpoint proof pub .S2 hash =
      ok (.Ok (p,a))) :
    CheckpointBytes4SavedFields.BodyMatches p a pm
      am ∧
    CheckpointBytes5Output.accumulator a =
      am ∧
    decodeAccumulator (bytesOf saved.val) = some (CheckpointBytes5Output.accumulator a) ∧
    a.next.val = 10 ∧ reserved = true := by
  have encoding : bytesOf checkpoint.val = encode H stored publicBytes pm
      am := by
    rw [same,tx1_saved,writer_bytes]
  have source := Tx2N_Install.reader_success base reserved query D hash checkpoint proof pub .S2 p a success
  have next : am.next=10 := ten
  obtain ⟨fields,cursor,allocation⟩ := CheckpointBytes4SuccessfulFields.successful_saved_fields
    reserved (VTop_Checkpoint.digest D) checkpoint proof pub hash p a H stored publicBytes
    pm _ encoding next source
  have observation := CheckpointBytes5Output.fields_observation p a _ _ fields cursor
  refine ⟨fields,observation.2.2,?_,cursor.trans next,allocation⟩
  rw [tx1_saved,writer_bytes,observation.2.2]
  exact decode_written H stored publicBytes pm _ next

#print axioms saved_ten
end AspisR1.F3N_ReaderNumeric
end
