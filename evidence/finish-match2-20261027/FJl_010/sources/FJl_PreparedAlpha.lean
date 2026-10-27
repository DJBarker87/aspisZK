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
  have at0 : Array.index_usize (Tx1Q_Carriers.prepared (currentPrepared out)).alpha 0#usize=
      ok (Tx1Q_Carriers.e (currentE (F3L_SourcePrepared.alpha out 0))) := by
    change Array.index_usize
      (Tx1Q_Carriers.arr Tx1Q_Carriers.e (AspisR1ClaimPreparedBridge.mapArray currentE out.alpha)) 0#usize=_
    unfold Array.index_usize
    change (match (out.alpha.val.map currentE |>.map Tx1Q_Carriers.e)[0]? with
      | none => fail .arrayOutOfBounds | some x => ok x)=_
    rw [List.getElem?_map,List.getElem?_map,
      List.getElem?_eq_getElem (by have h : out.alpha.val.length=2:=out.alpha.property; omega)]
    rfl
  have same := Result.ok.inj (read.symm.trans at0)
  rw [same]
  exact h
#print axioms value
end AspisR1.FJl_PreparedAlpha
end
