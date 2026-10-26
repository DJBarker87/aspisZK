import RPz7_TxS_Writer
import RPz7_TxS_RawTen
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.TxS_Encoding
open Tx1Q_Carriers AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
def Facts {CoreError H : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H} {hash : H}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (H : Bytes → State) : Prop :=
  ∃ pm : OraclePortCheckpointAbiC5.Prepared,
    saved=Tx2N_Reader.writer H (bytesOf proof.val) (bytesOf pub.val) pm
      (CheckpointBytes5Output.accumulator (accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}))

def Model {CoreError H : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H} {hash : H}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (parsed : Parsed) : Prop :=
  ∃ pm : OraclePortCheckpointAbiC5.Prepared,
    saved=Tx2N_Reader.writer H (bytesOf proof.val) (bytesOf pub.val) pm
      (CheckpointBytes5Output.accumulator (accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})) ∧
  ∀ (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (q : Fin 22 → Fin 262144) (raw : TxS_Carriers.Prefix) (rho : OraclePortCheckpointAbiC5.K),
    let tr := TxS_Carriers.toTyped raw
    let data := TxS_Carriers.data (typedRows parsed q tr)
    Port5Q1_QueryPorts.SessionAPrepare (prepared run.p) data q rho →
    LiteralMatchingData.read (typedRows parsed q tr)=some data →
    Port5Q1_GeometryCanonical.SessionAPrimitives geo →
    Port5Q1_Domain.SessionADomain geo →
    geo.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul →
    geo.op7=ok (1#u32) → geo.op11=Port4C_InverseExecution.inverse_owned →
    AuS1_Finish.Collision H trace parsed q ∨
      saved=Tx2N_Reader.writer H (bytesOf proof.val) (bytesOf pub.val) pm
        (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model data rho q)).accumulator

theorem model {CoreError H : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H} {hash : H}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (parsed : Parsed)
    (physical : Facts run H) (ten : TxS_RawTen.Outcome run H trace parsed) :
    Model run H trace parsed := by
  obtain ⟨pm,encoded⟩ := physical
  refine ⟨pm,encoded,?_⟩
  intro ports q raw rho
  dsimp only
  intro prepare read geoLeaves domain multiply one inverse
  rcases ten ports q raw rho prepare read geoLeaves domain multiply one inverse with collision | checked
  · exact Or.inl collision
  · right
    rw [encoded,checked.1]

#print axioms model
end AspisR1.TxS_Encoding
end
