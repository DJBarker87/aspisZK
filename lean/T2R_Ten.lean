import Tx1Q_Endpoint
import AuS1_Finish
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.T2R_Ten
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
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K),
    Port5Q1_QueryPorts.SessionAPrepare (prepared run.p) data q rho →
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

end AspisR1.T2R_Ten
end
