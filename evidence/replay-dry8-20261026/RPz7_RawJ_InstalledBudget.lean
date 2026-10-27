import RPz7_RawJ_CallerBudget
import RPz7_RawJ_WrapperBudget
import RPz7_GExq_InstalledWrapper
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_InstalledBudget
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd GExp_CountLaws

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem first {A : Type} (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state : A) :
    count 1018 (GExq_InstalledWrapper.first adapter ops stage finish reserved query geo B std hashv
      copy allocator e id data state) := by
  exact RawJ_WrapperBudget.first _ _
    (RawJ_CallerBudget.first adapter ops stage finish reserved query geo B std hashv id e.first data) _ _ _ _

theorem second {A : Type} (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state : A) :
    count 903 (GExq_InstalledWrapper.second adapter ops stage finish reserved query geo B std hashv
      allocator e id data slot state) := by
  exact RawJ_WrapperBudget.second _ _
    (RawJ_CallerBudget.second adapter ops stage finish reserved query geo B std hashv id (e.second secondSizes) data slot) _ _ _

#print axioms first
#print axioms second
end AspisR1.RawJ_InstalledBudget
end
