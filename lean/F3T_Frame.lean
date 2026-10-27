import F3T_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Frame
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment

theorem frame_eq (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (n : Nat) (bound : n≤33) :
    RawCutWordsFromView.frameFromView D (view (eval H (original D P))) n=
      RawCutWordsFromView.frame D H (eval H P).2.semantic.value (eval H P).2.proof n := by
  rw [F3T_Projection.original_view]
  change RawCutWordsFromView.frameFromView D
    (eval H (RawCutProverCompiler.experiment (F3T_Projection.project P)
      (OracleDecisionFeasibilityCore.verifier D
        (F3_Model.decision (eval H P).2.physical (eval H P).2.stored)))) n=_
  rw [OraclePortReplay.frameFromView_eq D _ _ H n bound,
    RawCutProverCompiler.experiment_eval,F3T_Projection.project_eval]
#print axioms frame_eq
end AspisR1.F3T_Frame
end
