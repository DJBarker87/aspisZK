import OraclePortAcceptedContextC6
import OraclePortFrozenOrderAccepted

/-! A byte-derived checkpoint stage, with no externally supplied prepared state.
The resumer authenticates and decodes the saved bytes and executes twelve steps.
Its returned accumulator, rather than an independently supplied sum, is checked. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozen2
open scoped BigOperators
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] QueryAccumulator.run22 QueryResidualBridge.values QueryResidualBridge.basis

abbrev completeState (i : SourceInputs) (q : Fin 22 → Fin 262144) :=
  QueryAccumulator.run22 LiteralOpeningView.eK (SelectedChallengeMap.rhoOf i.rho)
    (QueryResidualBridge.values i.data q) (QueryResidualBridge.basis q)

def finish (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs)
    (a : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E) : Bool :=
  D0TypedChecks.verify (typedRows p q tr) i &&
    decide ((∑ l : Fin 64, i.data.f l * LiteralOpeningView.eK (a.weights l)) = a.rhs)

def checkpoint (stored : Bytes) (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs) (v : LiteralOpeningView.View) :=
  OraclePortCheckpointOracleC5.writeResume stored tr.statement.pubBytes
    (OraclePortAcceptedContextC6.context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q

theorem checkpoint_value (H : Bytes → State) (stored : Bytes) (p : Parsed)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : SourceInputs) (v : LiteralOpeningView.View) :
    (eval H (checkpoint stored p q tr i v)).2 = some (completeState i q) :=
  OraclePortCheckpointOracleC5.writeResume_value H stored tr.statement.pubBytes _ _ _ q

theorem checkpoint_reads (H : Bytes → State) (stored : Bytes) (p : Parsed)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : SourceInputs) (v : LiteralOpeningView.View) :
    (eval H (checkpoint stored p q tr i v)).1.length = 6 :=
  OraclePortCheckpointOracleC5.writeResume_reads H stored tr.statement.pubBytes _ _ _ q

theorem finish_value (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs)
    (hi : input p q tr = some i) (hq : queries tr = some q) :
    finish p q tr i (completeState i q) = D0TypedChecks.verify (typedRows p q tr) i := by
  cases hc : D0TypedChecks.verify (typedRows p q tr) i
  · simp only [finish,hc,Bool.false_and]
  · have fields := (input_fields p q tr i hi).1
    have decoded : LiteralQueryRead.decode i.queryBytes = some q := by
      simpa [queries,fields.2.1] using hq
    have sum := (D0TypedChecks.accepted_backend _ i hc).2 q decoded
    simpa only [finish,hc,Bool.true_and,completeState,QueryAccumulator.run22_weights,
      QueryAccumulator.run22_rhs,decide_eq_true_eq,HchecksAccumulator.ClosedSum] using sum

#print axioms checkpoint_value
#print axioms checkpoint_reads
#print axioms finish_value
end AspisR1.OraclePortFrozen2
end
