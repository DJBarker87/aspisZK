import RPt_FJo_Tx1Powers
import RPt_FJo_Tx1GammaCanonical
import RPt_FJo_Tx1AlphaCanonical
import RPt_FJl_PreparedAlpha
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_NativeFirst
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
/-- Native TX1 operands from the actual preparation result and its literal projection. -/
theorem value {CoreError Hash : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (parsed : OraclePortCompactDraft.Parsed) (view : LiteralOpeningView.View)
    (q : Fin 22 → Fin 262144) (data : RecordedBinaryExperimentBin.SourceInputs)
    (same : currentPrepared out=run.p)
    (numeric : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context parsed data view) data.data (SelectedChallengeMap.rhoOf data.rho) q) :
    let g := FIp_DotsAdapter.toArray (Tx1Q_Carriers.arr Tx1Q_Carriers.e run.scratch)
    FIo_ArrayCanon.Holds g ∧
    (∀ l : Fin 29,FIp_ArrayValue.value g l.val=data.data.gamma^l.val) ∧
    CheckpointBytes5Output.ofE (Tx1Q_Carriers.prepared run.p).gamma=data.data.gamma ∧
    ∀ alpha,Array.index_usize (Tx1Q_Carriers.prepared run.p).alpha 0#usize=ok alpha →
      CheckpointBytes5Output.ofE alpha=data.data.alpha0 := by
  have source := FJo_Tx1Powers.value ops reserved query geo B std D hash pub publicBytes proof split saved run
  have gamma : CheckpointBytes5Output.ofE (Tx1Q_Carriers.prepared run.p).gamma=data.data.gamma := by
    rw [←same]
    exact FJl_PreparedGamma.value out parsed view q data numeric
  refine ⟨source.1,?_,gamma,?_⟩
  · intro l
    rw [source.2 l,gamma]
  · intro alpha read
    rw [←same] at read
    exact FJl_PreparedAlpha.value out parsed view q data numeric alpha read
#print axioms value
end AspisR1.FJp_NativeFirst
end
