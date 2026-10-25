import Tx2N_Install
import CheckpointBytes5Join
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Reader
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5

/-- The one writer equation requested from TX1 is equality of the actual Vec
with this physical encoding of the frozen ten-step state. -/
def writer (H : Bytes → State) (stored pub : Bytes) (pm : Prepared)
    (am : QueryAccumulator.State K E) : alloc.vec.Vec U8 :=
  ⟨(encode H stored pub pm am).map CheckpointBytes5Writer.u8,by
    simp only [List.length_map,encode_length]
    scalar_tac⟩

theorem writer_bytes (H : Bytes → State) (stored pub : Bytes) (pm : Prepared)
    (am : QueryAccumulator.State K E) :
    bytesOf (writer H stored pub pm am).val = encode H stored pub pm am :=
  CheckpointBytes5Writer.bytes_roundtrip _

/-- This reader half needs only the SAME saved Vec equation. The checkpoint
identity argument is supplied by RowOrder on the accepted pair, not by a new
semantic state obligation. No successful reader is independently selected. -/
theorem saved_ten (base : VTop_Stages.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (checkpoint proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (H : Bytes → State) (stored publicBytes : Bytes) (c : Context)
    (data : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144)
    (same : bytesOf checkpoint.val = bytesOf saved.val)
    (tx1_saved : saved = writer H stored publicBytes (prepared c data rho q)
      (OraclePortCheckpointStateC3.write (model data rho q)).accumulator)
    (success : (Tx2N_Install.inner base reserved query).op18 D checkpoint proof pub .S2 hash =
      ok (.Ok (p,a))) :
    CheckpointBytes4SavedFields.BodyMatches p a (prepared c data rho q)
      (OraclePortCheckpointStateC3.write (model data rho q)).accumulator ∧
    CheckpointBytes5Output.accumulator a =
      (OraclePortCheckpointStateC3.write (model data rho q)).accumulator ∧
    decodeAccumulator (bytesOf saved.val) = some (CheckpointBytes5Output.accumulator a) ∧
    a.next.val = 10 ∧ reserved = true := by
  have encoding : bytesOf checkpoint.val = encode H stored publicBytes (prepared c data rho q)
      (OraclePortCheckpointStateC3.write (model data rho q)).accumulator := by
    rw [same,tx1_saved,writer_bytes]
  have source := Tx2N_Install.reader_success base reserved query D hash checkpoint proof pub .S2 p a success
  have next := OraclePortCheckpointStateC3.saved_next (model data rho q)
  obtain ⟨fields,cursor,allocation⟩ := CheckpointBytes4SuccessfulFields.successful_saved_fields
    reserved (VTop_Checkpoint.digest D) checkpoint proof pub hash p a H stored publicBytes
    (prepared c data rho q) _ encoding next source
  have observation := CheckpointBytes5Output.fields_observation p a _ _ fields cursor
  refine ⟨fields,observation.2.2,?_,cursor.trans next,allocation⟩
  rw [tx1_saved,writer_bytes,observation.2.2]
  exact decode_written H stored publicBytes (prepared c data rho q) _ next

#print axioms writer_bytes
#print axioms saved_ten
end AspisR1.Tx2N_Reader
end
