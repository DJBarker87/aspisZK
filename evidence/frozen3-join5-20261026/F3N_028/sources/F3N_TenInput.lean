import F3N_Ten
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_TenInput
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4

theorem same_input {CoreError Hash : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash} {hash : Hash}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (p : Parsed)
    (ten : Cons_Ten.Outcome run H trace p)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : RecordedBinaryExperimentBin.SourceInputs)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p)
      i.data q (SelectedChallengeMap.rhoOf i.rho))
    (parser : OraclePortStoredParserC4.parseReached (MultiproofConeCanonical.bytesOf proof.val) tr=some p)
    (found : input p q tr=some i)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives geo)
    (domain : Port5Q1_Domain.SessionADomain geo)
    (multiply : geo.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geo.op7=ok (1#u32)) (inverse : geo.op11=Port4C_InverseExecution.inverse_owned) :
    let state := Tx1Q_Carriers.accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}
    AuS1_Finish.Collision H trace p q ∨
      (CheckpointBytes5Output.accumulator state=
        (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
          (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
      Port3_CheckpointInstall.writer (Tx1Q_Install.digest D) (Tx1Q_Carriers.prepared run.p)
        state proof pub hash=ok saved ∧ run.flushed.val.length=64 ∧ run.out.next.val=10) :=
  ten ports q tr i.data (SelectedChallengeMap.rhoOf i.rho) prepare parser (input_fields p q tr i found).2
    canonical domain multiply one inverse

#print axioms same_input
end AspisR1.F3N_TenInput
end
