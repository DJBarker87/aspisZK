import F3J_SamplerStep
import F3M_ChallengeTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_SamplerStepErasure
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
/-- Literal words do not alter a sampler step when the physical erased prefix
and message agree. The complete issued log and reply are retained. -/
theorem value (H : Bytes → State) (row : Nat) (P Q : LiteralTranscript.Prefix)
    (m n : LiteralTranscript.Message)
    (samePrefix : LiteralTranscript.erasePrefix P=LiteralTranscript.erasePrefix Q)
    (message : LiteralTranscript.erase m=LiteralTranscript.erase n) :
    eval H (LiteralByteSampler.samp row P m).toProgram=
      eval H (LiteralByteSampler.samp row Q n).toProgram := by
  rw [LiteralByteSampler.eval_eq,LiteralByteSampler.eval_eq]
  unfold LiteralTranscript.samp
  rw [samePrefix,message]
#print axioms value
end AspisR1.FJq_SamplerStepErasure
end
