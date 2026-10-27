import RPz7_RawJ_FirstOuter
import RPz7_RawJ_SecondOuter
import RPz7_RawJ_ChildBudget
import RPz7_GExq_Caller
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_CallerBudget
open Aeneas Aeneas.Std Result GExp_CountLaws

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem first (id : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
    (data : Slice U8) :
    count 1018 (GExq_Caller.first adapter ops stage finish reserved query geo B std hashv id accounts data) := by
  exact RawJ_OuterBudget.lower_count _
    (fun call => RawJ_ChildBudget.child adapter ops stage finish reserved query geo B std hashv call)
    _ _ (RawJ_FirstOuter.first _ _ _ _)

theorem second (id : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    count 903 (GExq_Caller.second adapter ops stage finish reserved query geo B std hashv id accounts data slot) := by
  exact RawJ_OuterBudget.lower_count _
    (fun call => RawJ_ChildBudget.child adapter ops stage finish reserved query geo B std hashv call)
    _ _ (RawJ_SecondOuter.second _ _ _ _ _)

#print axioms first
#print axioms second
end AspisR1.RawJ_CallerBudget
end
