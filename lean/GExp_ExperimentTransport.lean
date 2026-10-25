import GExp_GlobalBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_ExperimentTransport
open Aeneas Aeneas.Std Result GExp_Experiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem accepted (current : AspisR1CurrentCaller.Ops) (stage : VTop_Stages.Ops) (reserved : Bool)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D1 : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (D2 : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (adversary : Program Bytes State FirstInputs)
    (chooseSecond : FirstInputs → alloc.vec.Vec U8 → Program Bytes State SecondInputs)
    (H : Bytes → State) (input : FirstInputs) (next : SecondInputs) (saved : alloc.vec.Vec U8)
    (prefixLog firstLog choiceLog secondLog : List (Bytes × State))
    (start : eval H adversary = (prefixLog,input))
    (firstRun : eval H (first current B std hashv D1 input) = (firstLog,ok (.Ok saved)))
    (choice : eval H (chooseSecond input saved) = (choiceLog,next))
    (secondRun : eval H (second stage reserved hashv D2 next) = (secondLog,ok (.Ok ()))) :
    eval H (program current stage reserved B std hashv D1 D2 adversary chooseSecond) =
      (prefixLog ++ firstLog ++ choiceLog ++ secondLog,
        input,ok (.Ok saved),some (next,ok (.Ok ()))) := by
  simp only [program,eval_bind,start,firstRun,choice,secondRun,eval,List.append_nil,List.append_assoc]

/-- Rejected first returns retain their complete earlier reads and execute
neither adaptive second-submission code nor a fabricated successful suffix. -/
theorem rejected_first (current : AspisR1CurrentCaller.Ops) (stage : VTop_Stages.Ops) (reserved : Bool)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D1 : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (D2 : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (adversary : Program Bytes State FirstInputs)
    (chooseSecond : FirstInputs → alloc.vec.Vec U8 → Program Bytes State SecondInputs)
    (H : Bytes → State) (input : FirstInputs) (reply : FirstReply)
    (prefixLog firstLog : List (Bytes × State))
    (start : eval H adversary = (prefixLog,input))
    (firstRun : eval H (first current B std hashv D1 input) = (firstLog,reply))
    (rejected : ∀ saved, reply ≠ ok (.Ok saved)) :
    eval H (program current stage reserved B std hashv D1 D2 adversary chooseSecond) =
      (prefixLog ++ firstLog,input,reply,none) := by
  cases reply with
  | fail e => simp only [program,eval_bind,start,firstRun,eval,List.append_nil]
  | div => simp only [program,eval_bind,start,firstRun,eval,List.append_nil]
  | ok result => cases result with
    | Err e => simp only [program,eval_bind,start,firstRun,eval,List.append_nil]
    | Ok saved => exact False.elim (rejected saved rfl)

#print axioms accepted
#print axioms rejected_first
end AspisR1.GExp_ExperimentTransport
end
