import DrvC_AuthenticatedCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_SecondProgram
open Aeneas Aeneas.Std Result VTop_Stages
open DrvC_Installation DrvC_Effects DrvC_Flow
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult

/-- All outcomes, complete ordered digest program, not only verdict equality. -/
theorem program {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (pub proof checkpoint : Slice U8) :
    VTop_OracleCode.interpret (DrvC_Implementation.implementation c)
      (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects (digest c) pub proof checkpoint () none) =
    GExp_Experiment.second (stage c) c.reserved hashv (digest c) ⟨pub,proof,checkpoint⟩ := by
  rw [← DrvC_CallCode.program_lower,DrvC_SecondFlow.tx2_authenticated,DrvC_AuthenticatedCode.code c hashv]
  rfl

#print axioms program
end AspisR1.DrvC_SecondProgram
end
