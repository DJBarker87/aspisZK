import F3X_FinishFields
import F3V_ReadModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_ReadModel
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem fields {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (t : Cons_Native.Witness)
    (calls : Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved c.query c.geometry
      (D2 c H) () e.pub e.proof e.saved.deref t)
    (p : OraclePortCompactDraft.Parsed) (data : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View) (q : Fin 22 → Fin 262144)
    (saved : e.saved=Tx2N_Reader.writer H (bytesOf e.proof.val) (bytesOf e.pub.val)
      (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p data v)
        data.data (SelectedChallengeMap.rhoOf data.rho) q)
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model data.data
        (SelectedChallengeMap.rhoOf data.rho) q)).accumulator) : F3X_FinishFields.Holds t.p2 data.data := by
  have result := F3N_ReaderNumeric.saved_ten (Op5T_Concrete.stage (AuS1_Install.base c.stageBase))
    c.reserved c.query (D2 c H) () e.saved.deref e.proof e.pub e.saved t.p2 t.saved2 H
    _ _ _ _ (by rfl) rfl saved calls.1
  exact F3X_FinishFields.from_fields t.p2 t.saved2 p data v q _ result.1

#print axioms fields
end AspisR1.F3X_ReadModel
end
