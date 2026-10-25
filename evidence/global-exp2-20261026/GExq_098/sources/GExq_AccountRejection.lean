import GExq_AccountExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_AccountRejection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment

theorem failed_prefix {A F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A))
    (H : Bytes → State) (error : Error)
    (failed : let input := (eval H adversary).2
      (eval H (SdkC_Oracle.program (GExq_InstalledWrapper.first adapter ops stage finish reserved query geo B std hashv
        copy allocator input.entry id input.data input.state))).2 = .fail error) :
    let input := (eval H adversary).2
    let first := eval H (SdkC_Oracle.program (GExq_InstalledWrapper.first adapter ops stage finish reserved query geo B std hashv
        copy allocator input.entry id input.data input.state))
    eval H (program adapter ops stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond) =
      ((eval H adversary).1 ++ first.1,(input,.fail error,none)) := by
  dsimp only
  simp only [program,eval_bind,failed,eval,List.append_nil]

#print axioms failed_prefix
end AspisR1.GExq_AccountRejection
end
