import Tx1Q_SameCut
import Tx1Q_Model
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_Endpoint
open Tx1Q_Carriers AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4

/-- Explicit remaining gates. This conditional endpoint does NOT discharge
parsing/transcript, matching-data, selected-map authentication, or owner laws.
It uses the run's own preparation, geometry, scratch and checkpoint. -/
def WhenBound {CoreError H : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H} {hash : H}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved) : Prop :=
  ∀ (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K),
    Port5Q1_QueryPorts.SessionAPrepare (prepared run.p) data q rho →
    OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr = some parsed →
    LiteralMatchingData.read (typedRows parsed q tr) = some data →
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

theorem on_run {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (length : proof.val.length = 57607) : WhenBound run := by
  intro ports parsed q tr data rho prepare parser read recovered authenticated canonical domain multiply one inverse
  exact Tx1Q_Model.ten installed reserved query geo D hash semantic pub proof split saved run ports
    parsed q tr data rho prepare read (OraclePortStoredParserC4.parsed _ _ _ parser).2.1 length
    recovered authenticated canonical domain multiply one inverse

theorem reached {CoreError : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      accounts1 accounts2 saved f s)
    (length : f.proof.val.length = 57607) :
    ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std) reserved query geo
      (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
      WhenBound run := by
  obtain ⟨run⟩ := Tx1Q_SameCut.reached adapterOps ops reserved query geo B std accounts1 accounts2 saved f s cuts
  exact ⟨run,on_run _ _ _ _ _ _ _ _ _ _ _ run length⟩

#print axioms on_run
#print axioms reached
#print WhenBound
end AspisR1.Tx1Q_Endpoint
end
