import Tx1Q_Execution
import Tx1Q_Initial
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_Model
open Tx1Q_Carriers
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
attribute [local irreducible] OraclePortCheckpointStateC3.advance QueryResidualBridge.values QueryResidualBridge.basis
  Port3_CheckpointInstall.writer

/-- Q1's same-run endpoint on the concrete CurrentCaller installation.
The remaining parser/data/authentication gates are explicit, not a global
ObservationBinding or an independently selected query/flush/writer success. -/
theorem ten {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geoOps D hash semantic pub proof split saved)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (prepared run.p) data q rho)
    (read : LiteralMatchingData.read (typedRows parsed q tr) = some data)
    (wire : parsed.wire = bytesOf proof.val) (proofLength : proof.val.length = 57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos < 22 → recovered (index q 2 pos) =
      some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (geometryCanonical : Port5Q1_GeometryCanonical.SessionAPrimitives geoOps)
    (domain : Port5Q1_Domain.SessionADomain geoOps)
    (multiply : geoOps.op9 = AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geoOps.op7 = ok (1#u32))
    (inverse : geoOps.op11 = Port4C_InverseExecution.inverse_owned) :
    let state := accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}
    CheckpointBytes5Output.accumulator state =
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model data rho q)).accumulator ∧
    Port3_CheckpointInstall.writer (Tx1Q_Install.digest D) (prepared run.p) state proof pub hash = ok saved ∧
    run.flushed.val.length = 64 ∧ run.out.next.val = 10 := by
  have geometry := Port5Q1_GeometryReads.accepted geoOps geometryCanonical domain multiply one inverse
    run.p.queries 0#usize 10#usize (Tx1Q_Carriers.geometry run.geometry) (by decide) run.geometry_call
  have init := Tx1Q_Initial.fields reserved (accumulator run.initial) run.initial_call
  have block := Port5Q1_QueryBlock.materialized (Port3_QueryStage.release query)
    (Tx1Q_QueryBridge.release_ports query ports) proof (prepared run.p) (accumulator run.initial)
    (accumulator run.out) (arr e run.scratch) none (Tx1Q_Carriers.geometry run.geometry)
    (pending run.pending) (pending run.after) parsed q tr data rho prepare read wire proofLength
    recovered authenticated 0#usize 10#usize geometry init.2.1 init.1 init.2.2.1 init.2.2.2.1
    reserved run.pending_call run.query_call (slice k run.flushed) run.flush_call
  have meaning := block.1
  rw [init.2.2.2.2] at meaning
  have final := meaning.trans (Port5Q1_Recurrence.ten _)
  refine ⟨?_,run.writer_call,?_,block.2.2.1⟩
  · simpa only [Tx1Q_Carriers.materialize] using final
  · simpa only [slice,List.length_map] using block.2.1

#print axioms ten
end AspisR1.Tx1Q_Model
end
