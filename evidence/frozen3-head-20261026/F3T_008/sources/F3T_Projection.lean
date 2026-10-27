import F3T_Experiment
import OraclePortStoredProjectionC4
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Projection
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open F3T_Experiment

def project (P : Prover) : RawCutProverCompiler.Prover :=
  bind P fun i => .done (i.semantic.value,i.proof)

theorem project_eval (P : Prover) (H : Bytes → State) :
    eval H (project P)=((eval H P).1,((eval H P).2.semantic.value,(eval H P).2.proof)) := by
  simp only [project,eval_bind,eval,List.append_nil]

/-- A pointwise identity, never an oracle-dependent decision experiment. Both
physical P and stored S are selected by the actual adaptive F3 prover. -/
theorem original_view (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    view (eval H (original D P))=
      eval H (OraclePortExperiment.original D
        (F3_Model.decision (eval H P).2.physical (eval H P).2.stored) (project P)) := by
  rw [original_eval,OraclePortExperiment.original,OracleDecisionFeasibilityCore.original,
    RawCutProverCompiler.experiment_eval,project_eval]
  rfl

theorem recorded_view (D : LiteralByteProtocol.Decoder)
    (build : RawCutProverCompiler.RunView → CanonicalCutEnrichedTranscript.Words)
    (P : Prover) (H : Bytes → State) :
    view (eval H (recorded D build P))=
      eval H (OracleDecisionPrereqStarts.annotated D
        (F3_Model.decision (eval H P).2.physical (eval H P).2.stored) build (project P)) := by
  rw [recorded_eval,OracleDecisionPrereqStarts.annotated,
    OracleDecisionFeasibilityCompiler.compiled_experiment_eval]
  have same := original_view D P H
  change view (eval H (original D P))=
    eval H (RawCutProverCompiler.experiment (project P)
      (OraclePortExperiment.verifier D
        (F3_Model.decision (eval H P).2.physical (eval H P).2.stored))) at same
  rw [←same]
  have physical : (eval H (original D P)).2.1.physical=(eval H P).2.physical := by rw [original_eval]
  have stored : (eval H (original D P)).2.1.stored=(eval H P).2.stored := by rw [original_eval]
  simp only [view,enrich,F3_Model.verifier,OraclePortStoredExperimentC4.verifier]
  rw [physical,stored]

#print axioms project_eval
#print axioms original_view
#print axioms recorded_view
end AspisR1.F3T_Projection
end
