import FJl_PreparedGamma
import FJc_ReadSlot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_PreparedAlpha
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1CurrentCaller.InstalledPreparation
/-- SAME alpha0, transported by coordinate from the installed numeric Prepared. -/
theorem value (out : verifier.Prepared) (p : OraclePortCompactDraft.Parsed)
    (v : LiteralOpeningView.View) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (numeric : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p data v) data.data (SelectedChallengeMap.rhoOf data.rho) q)
    (a0 : AspisR1Stage2.Stage2Finish.E)
    (read : Array.index_usize (Tx1Q_Carriers.prepared (currentPrepared out)).alpha 0#usize=ok a0) :
    CheckpointBytes5Output.ofE a0=data.data.alpha0 := by
  have h := congrArg (fun x : OraclePortCheckpointAbiC5.Prepared=>x.alpha 0) numeric
  have slot := FJc_ReadSlot.slot _ _ _ read
  change (out.alpha.val.map currentE |>.map Tx1Q_Carriers.e)[0]?=some a0 at slot
  rw [List.getElem?_map,List.getElem?_map,
    List.getElem?_eq_getElem (by have h : out.alpha.val.length=2:=out.alpha.property; omega)] at slot
  have same := Option.some.inj slot
  rw [←same]
  exact h
#print axioms value
end AspisR1.FJl_PreparedAlpha
end
