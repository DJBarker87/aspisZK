import OraclePortExperiment
import R9PoolSavedTenModel

/-! Logical saved-ten/resumed-twelve model with an effectful terminal.
The terminal runs on resume before compiler replay. Physical ABI and Rust
interleaving are separate; this model does not claim an on-chain schedule. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCheckpoint
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler (Public Proof Prover RunView experiment)
open OraclePortExperiment (Decision verifier original recorded)
open R9PoolSavedTenModel (Raw Checkpoint rounds prepare write write_raw stage1)

/-- Full terminal log is retained, rather than assigning an effectful
decision the old sampler-only log. -/
def base (dO : Decision) (raw : Raw) : Program Bytes State RunView :=
  bind (OracleProgramRecording.record (OracleDecisionFeasibilityCore.onBytes dO
    raw.2.2 (raw.2.1.2 33))) fun terminal =>
    .done (raw.1 ++ terminal.1, (raw.2.1, terminal.2))

theorem rounds_terminal (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (pf : Proof) (H : Bytes → State) (n : Nat) (t : LiteralTranscript.Prefix) :
    eval H (OracleDecisionFeasibilityCore.verifierFrom D dO pf n t) =
      let r := eval H (rounds D pf n t)
      let terminal := eval H (OracleDecisionFeasibilityCore.onBytes dO r.2 (pf 33))
      (r.1 ++ terminal.1, terminal.2) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [OracleDecisionFeasibilityCore.verifierFrom, rounds, eval_bind, ih]
    simp only [List.append_assoc]

theorem prepare_original (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (P : Prover) (H : Bytes → State) :
    (eval H (base dO (eval H (prepare D P)))).2 = eval H (original D dO P) := by
  have hv := rounds_terminal D dO (eval H P).2.2 H 33 (FS.emptyPrefix (eval H P).2.1)
  change eval H (verifier D dO (eval H P).2.1 (eval H P).2.2) = _ at hv
  unfold original OracleDecisionFeasibilityCore.original
  rw [RawCutProverCompiler.experiment_eval, hv]
  simp only [base, prepare, eval_bind, OracleProgramRecording.eval_record, eval,
    List.append_nil, List.append_assoc]

/-- Execute the terminal once, then replay the complete verifier. -/
def resume (D : LiteralByteProtocol.Decoder) (dO : Decision) (c : Checkpoint) :
    Program Bytes State RunView :=
  bind (base dO c.raw) fun orig =>
    bind (OracleProgramRecording.record (verifier D dO orig.2.1.1 orig.2.1.2)) fun replay =>
      .done (orig.1 ++ replay.1,
        ((orig.2.1.1, RawCutTranscriptRun.proof
          (BinCompiledRunWordStability.wordsFromRun D orig) orig.2.1.2),
        R16DecisionCheckpoint.tx2 (R16DecisionCheckpoint.resume c.saved) && orig.2.2))

theorem resume_matching (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (raw : Raw) (c : Checkpoint) (H : Bytes → State)
    (hw : write raw = some c) (ha : (eval H (resume D dO c)).2.2.2 = true) :
    c.saved.next = 10 ∧ ∀ j, MatchingSupport.match0 c.saved.data (c.saved.queries j) := by
  have hc : R16DecisionCheckpoint.tx2 (R16DecisionCheckpoint.resume c.saved) = true := by
    simp only [resume, eval_bind, OracleProgramRecording.eval_record, eval] at ha
    exact (Bool.and_eq_true_iff.mp ha).1
  have hpure : R9PoolSavedTenModel.accepted (fun _ _ => true) c = true := by
    simp only [R9PoolSavedTenModel.accepted, R9PoolSavedTenModel.base,
      RawCutTranscriptRun.decisionOnBytes, Bool.and_true]
    exact hc
  exact R9PoolSavedTenModel.accepted_matching (fun _ _ => true) raw c hw hpure

theorem resume_recorded (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (P : Prover) (H : Bytes → State) (c : Checkpoint)
    (hc : write (eval H (prepare D P)) = some c)
    (ha : (eval H (resume D dO c)).2.2.2 = true) :
    (eval H (resume D dO c)).2 = eval H (recorded D dO P) := by
  have hr := write_raw _ c hc
  have hb : (eval H (base dO c.raw)).2 = eval H (original D dO P) := by
    rw [hr]
    exact prepare_original D dO P H
  have ha' := ha
  simp only [resume, eval_bind, OracleProgramRecording.eval_record, eval] at ha'
  have hguard := (Bool.and_eq_true_iff.mp ha').1
  have hacc : (eval H (original D dO P)).2.2 = true := by
    rw [← hb]
    exact (Bool.and_eq_true_iff.mp ha').2
  unfold recorded OracleDecisionPrereqStarts.annotated
  rw [OracleDecisionFeasibilityCompiler.compiled_experiment_eval]
  simp only [resume, eval_bind, OracleProgramRecording.eval_record, eval]
  rw [hb, hguard, Bool.true_and, hacc]

#print axioms rounds_terminal
#print axioms prepare_original
#print axioms resume_matching
#print axioms resume_recorded
end AspisR1.OraclePortCheckpoint
end
