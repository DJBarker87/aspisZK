import GExq_Caller
import GExp_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_Nonvacuity
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

def emptyAccounts : S2W_ExtractionBoundary.Accounts := ⟨[],Nat.zero_le _⟩

/-- The new containing caller has a literal rejecting original submission,
without a successful child, chosen trace or syscall totality condition. -/
theorem second_rejects {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (H : Bytes → State) :
    eval H (SdkC_Oracle.program (GExq_Caller.second adapter ops stage finish reserved query geo B std
      hashv id emptyAccounts data slot)) =
      ([],ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData)) := by
  have different : (Slice.len emptyAccounts != 7#usize) = true := by decide
  simp only [GExq_Caller.second,S2W_Outer.stage2_owned,different,↓reduceIte,GExq_OuterLower.lower,
    SdkC_Oracle.program,eval]
  rfl

#print axioms second_rejects
#print axioms GExp_Nonvacuity.partial_syscall
#print axioms GExp_Nonvacuity.failed_attempt
end AspisR1.GExq_Nonvacuity
end
