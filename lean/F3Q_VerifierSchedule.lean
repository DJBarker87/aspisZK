import F3_Model
import F3K_SamplerProtocol
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_VerifierSchedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem evaluation (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input) :
    eval H (F3_Model.verifier D i)=
      let sampler := eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))
      let terminal := eval H (OracleDecisionFeasibilityCore.onBytes
        (F3_Model.decision i.physical i.stored) sampler.2 (i.proof 33))
      (sampler.1++terminal.1,terminal.2) := by
  rw [F3K_SamplerProtocol.initial D H i.semantic.value i.proof 33]
  exact F3_Model.complete_schedule D H i

#print axioms evaluation
end AspisR1.F3Q_VerifierSchedule
end
