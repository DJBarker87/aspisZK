import Tx1Q_Endpoint
import Tx1Q_SameCut
import Tx1Q_Model
import Tx1Q_Control
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PFin_Endpoint
open Tx1Q_Carriers AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4

/-- Source-specialized WhenBound endpoint. Parser/read/preparation arguments
are consumed by `consume`; indexed recovery and owner laws stay explicit.
This auxiliary pure endpoint is not added to deployed, whose collision-aware
PFin_Ten conclusion derives authentication internally. -/
def Outcome {CoreError H : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H} {hash : H}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K) : Prop :=
  ∀ (ports : Port5Q1_QueryPorts.SessionAPrimitives query),
    ∀ recovered : Nat → Option Bytes,
    (∀ pos, pos < 22 → recovered (index q 2 pos) = some (OraclePortPackedChoiceC4.payload parsed 2 pos)) →
    Port5Q1_GeometryCanonical.SessionAPrimitives geo →
    Port5Q1_Domain.SessionADomain geo →
    geo.op9 = AspisR1Qm31ArithmeticProbe.field.M31.mul →
    geo.op7 = ok (1#u32) → geo.op11 = Port4C_InverseExecution.inverse_owned →
    let state := accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}
    CheckpointBytes5Output.accumulator state =
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model data rho q)).accumulator ∧
    Port3_CheckpointInstall.writer (Tx1Q_Install.digest D) (prepared run.p) state proof pub hash = ok saved ∧
    run.flushed.val.length = 64 ∧ run.out.next.val = 10

theorem consume {CoreError H : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H} {hash : H}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (prepared run.p) data q rho)
    (parser : OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr = some parsed)
    (read : LiteralMatchingData.read (typedRows parsed q tr) = some data)
    (old : Tx1Q_Endpoint.WhenBound run) : Outcome run parsed q tr data rho := by
  intro ports recovered authenticated canonical domain multiply one inverse
  exact old ports parsed q tr data rho prepare parser read recovered authenticated canonical domain multiply one inverse

#print axioms consume
end AspisR1.PFin_Endpoint
end
