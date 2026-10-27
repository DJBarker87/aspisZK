import RPz8_FGl_PreparedAt
import RPz7_F3L_SourcePrepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_PreparedGamma
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1CurrentCaller.InstalledPreparation
/-- Transport the SAME prepared gamma through the existing numeric projection. -/
theorem value (out : verifier.Prepared) (p : OraclePortCompactDraft.Parsed)
    (v : LiteralOpeningView.View) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (numeric : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p data v) data.data (SelectedChallengeMap.rhoOf data.rho) q) :
    CheckpointBytes5Output.ofE (Tx1Q_Carriers.prepared (currentPrepared out)).gamma=data.data.gamma := by
  have h := congrArg (fun x : OraclePortCheckpointAbiC5.Prepared=>x.gamma) numeric
  exact h
#print axioms value
end AspisR1.FJl_PreparedGamma
end
