import F3_Model
import Tx2N_Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_ReaderPhysical
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem saved_ten {Hash : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (checkpoint proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (out : verifier.Prepared) (a : verifier.Accumulator)
    (H : Bytes → State) (physical : F3_Model.PhysicalPublic) (stored : Bytes)
    (p : OraclePortCompactDraft.Parsed) (i : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View) (q : Fin 22 → Fin 262144)
    (same : MultiproofConeCanonical.bytesOf checkpoint.val=MultiproofConeCanonical.bytesOf saved.val)
    (writer : saved=Tx2N_Reader.writer H stored physical.bytes
      (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p i v)
        i.data (SelectedChallengeMap.rhoOf i.rho) q)
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (success : (Tx2N_Install.inner base reserved query).op18 D checkpoint proof pub .S2 hash=ok (.Ok (out,a))) :
    CheckpointBytes4SavedFields.BodyMatches out a
      (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p i v)
        i.data (SelectedChallengeMap.rhoOf i.rho) q)
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
    CheckpointBytes5Output.accumulator a=
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
    OraclePortCheckpointResumeC5.decodeAccumulator (MultiproofConeCanonical.bytesOf saved.val)=
      some (CheckpointBytes5Output.accumulator a) ∧ a.next.val=10 ∧ reserved=true :=
  Tx2N_Reader.saved_ten base reserved query D hash checkpoint proof pub saved out a H stored physical.bytes
    (OraclePortAcceptedContextC6.context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q same writer success

#print axioms saved_ten
end AspisR1.F3N_ReaderPhysical
end
