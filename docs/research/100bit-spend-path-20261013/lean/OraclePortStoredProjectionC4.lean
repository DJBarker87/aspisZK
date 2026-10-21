import OraclePortStoredExperimentC4
import OraclePortReplay

/-! Pointwise bridge to existing replay lemmas. The fixed old decision below
is instantiated at one H for a theorem, not installed as an oracle-dependent
experiment or used under a probability law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredProjectionC4
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4

def project (P : Prover) : RawCutProverCompiler.Prover :=
  bind P fun i => .done (i.statement,i.proof)

theorem project_eval (P : Prover) (H : Bytes → State) :
    eval H (project P) = ((eval H P).1,((eval H P).2.statement,(eval H P).2.proof)) := by
  simp only [project,eval_bind,eval,List.append_nil]

theorem original_view (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    OraclePortStoredExperimentC4.view (eval H (original D d P)) =
      eval H (OraclePortExperiment.original D (d (eval H P).2.stored) (project P)) := by
  rw [original_eval,OraclePortExperiment.original,OracleDecisionFeasibilityCore.original,
    RawCutProverCompiler.experiment_eval,project_eval]
  rfl

theorem recorded_view (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → CanonicalCutEnrichedTranscript.Words)
    (P : Prover) (H : Bytes → State) :
    view (eval H (recorded D d build P)) =
      eval H (OracleDecisionPrereqStarts.annotated D (d (eval H P).2.stored) build (project P)) := by
  rw [recorded_eval,OracleDecisionPrereqStarts.annotated,
    OracleDecisionFeasibilityCompiler.compiled_experiment_eval]
  have same := original_view D d P H
  change view (eval H (original D d P)) =
    eval H (RawCutProverCompiler.experiment (project P)
      (OraclePortExperiment.verifier D (d (eval H P).2.stored))) at same
  rw [← same]
  have stored : (eval H (original D d P)).2.1.stored = (eval H P).2.stored := by
    rw [original_eval]
  simp only [view,enrich,OraclePortStoredExperimentC4.verifier]
  rw [stored]

/-- Exact frame identity is inherited pointwise, including the complete
sampler prefix and all terminal reads in the original trace. -/
theorem frame_eq (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (n : Nat) (hn : n ≤ 33) :
    RawCutWordsFromView.frameFromView D (view (eval H (original D d P))) n =
      RawCutWordsFromView.frame D H (eval H P).2.statement (eval H P).2.proof n := by
  rw [original_view]
  change RawCutWordsFromView.frameFromView D
    (eval H (RawCutProverCompiler.experiment (project P)
      (OracleDecisionFeasibilityCore.verifier D (d (eval H P).2.stored)))) n = _
  rw [OraclePortReplay.frameFromView_eq D _ _ H n hn,
    RawCutProverCompiler.experiment_eval,project_eval]

#print axioms project_eval
#print axioms original_view
#print axioms recorded_view
#print axioms frame_eq
end AspisR1.OraclePortStoredProjectionC4
end
