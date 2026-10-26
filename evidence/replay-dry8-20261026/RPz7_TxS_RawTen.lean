import RPz7_T2R_Ten
import RPz7_TxS_Carriers
import RPz7_AuS1_Finish
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.TxS_RawTen
open Tx1Q_Carriers AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
def Outcome {CoreError H : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H} {hash : H}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (parsed : Parsed) : Prop :=
  ∀ (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (q : Fin 22 → Fin 262144) (raw : TxS_Carriers.Prefix) (rho : OraclePortCheckpointAbiC5.K),
    let tr := TxS_Carriers.toTyped raw
    let data := TxS_Carriers.data (typedRows parsed q tr)

    ∀ _ : Port5Q1_QueryPorts.SessionAPrepare (prepared run.p) data q rho,
    LiteralMatchingData.read (typedRows parsed q tr) = some data →
    Port5Q1_GeometryCanonical.SessionAPrimitives geo →
    Port5Q1_Domain.SessionADomain geo →
    geo.op9 = AspisR1Qm31ArithmeticProbe.field.M31.mul →
    geo.op7 = ok (1#u32) → geo.op11 = Port4C_InverseExecution.inverse_owned →
    let state := accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}
    AuS1_Finish.Collision H trace parsed q ∨
    (CheckpointBytes5Output.accumulator state =
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model data rho q)).accumulator ∧
    Port3_CheckpointInstall.writer (Tx1Q_Install.digest D) (prepared run.p) state proof pub hash = ok saved ∧
    run.flushed.val.length = 64 ∧ run.out.next.val = 10 )

theorem of_typed {CoreError H : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H} {hash : H}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (parsed : Parsed)
    (old : T2R_Ten.Outcome run H trace parsed) : Outcome run H trace parsed := by
  intro ports q raw rho
  dsimp only
  exact old ports q _ _ rho

theorem to_typed {CoreError H : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H} {hash : H}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (parsed : Parsed)
    (new : Outcome run H trace parsed) : T2R_Ten.Outcome run H trace parsed := by
  intro ports q tr d rho prepare read geoLeaves domain multiply one inverse
  have transported := new ports q (TxS_Carriers.erase tr) rho
  dsimp only at transported
  rw [TxS_Carriers.prefix_erase,TxS_Carriers.data_of_read _ d read] at transported
  exact transported prepare read geoLeaves domain multiply one inverse

#print axioms of_typed
#print axioms to_typed
end AspisR1.TxS_RawTen
end
