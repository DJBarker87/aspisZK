import OraclePortTerminalCarrierAuditC3

/-! Lift the concrete carrier obstruction to the actual experiment. This is
negative evidence, not an all-rejecting substitute soundness headline. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortAcceptanceCarrierObstructionC3
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open RawCutProverCompiler (Prover)
open OraclePortExperiment (original recorded)
open OraclePortAdmission (admit)

theorem guarded_rejects (H : Bytes → State)
    (tr : RawCutTranscriptRun.ErasedPrefix) (m : RawCutTranscriptRun.ErasedMessage) :
    eval H (admit OraclePortBatchDraft.decision tr m) = ([],false) := by
  unfold admit
  split
  · exact OraclePortTerminalCarrierAuditC3.batch_always_rejects H tr m
  · rfl

theorem original_rejects (D : LiteralByteProtocol.Decoder) (P : Prover)
    (H : Bytes → State) :
    (eval H (original D (admit OraclePortBatchDraft.decision) P)).2.2 = false := by
  rw [original,OracleDecisionFeasibilityCore.original,RawCutProverCompiler.experiment_eval,
    OracleDecisionFeasibilityBudget.verifier_eval]
  exact congrArg Prod.snd (guarded_rejects H _ _)

theorem recorded_rejects (D : LiteralByteProtocol.Decoder) (P : Prover)
    (H : Bytes → State) :
    (eval H (recorded D (admit OraclePortBatchDraft.decision) P)).2.2 = false := by
  rw [recorded,OracleDecisionPrereqStarts.annotated,
    OracleDecisionFeasibilityCompiler.compiled_experiment_eval]
  exact original_rejects D P H

/-- Any accepting implementation rules out an acceptance-preserving join to
this decision. The accepting implementation is not postulated to exist. -/
theorem accepting_join_impossible (D : LiteralByteProtocol.Decoder) (P : Prover)
    (H : Bytes → State) (implementationAccepted : Bool) (ha : implementationAccepted = true) :
    implementationAccepted ≠
      (eval H (original D (admit OraclePortBatchDraft.decision) P)).2.2 := by
  rw [ha,original_rejects]
  decide

#print axioms guarded_rejects
#print axioms original_rejects
#print axioms recorded_rejects
#print axioms accepting_join_impossible
end AspisR1.OraclePortAcceptanceCarrierObstructionC3
end
