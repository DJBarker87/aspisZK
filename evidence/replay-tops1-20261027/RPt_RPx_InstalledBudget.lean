import RPt_RPx_ChildBudget
import RPt_RPx_OuterStage1
import RPt_RPx_OuterStage2
import RPt_RPx_WrapperBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_InstalledBudget
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open GExp_CountLaws
variable {A F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem first
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (state : A) :
    count 1018 (GExq_InstalledWrapper.first adapter ops stage finish reserved query geo B std hashv
      copy allocator e id data state) := by
  apply RPx_WrapperBudget.first
  apply RPx_LowerBudget.lower
  · exact RPx_ChildBudget.children adapter ops stage finish reserved query geo B std hashv
  · exact RPx_OuterStage1.stage1 _ _ _ _

theorem second
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state : A) :
    count 903 (GExq_InstalledWrapper.second adapter ops stage finish reserved query geo B std hashv
      allocator e id data slot state) := by
  apply RPx_WrapperBudget.second
  apply RPx_LowerBudget.lower
  · exact RPx_ChildBudget.children adapter ops stage finish reserved query geo B std hashv
  · exact RPx_OuterStage2.stage2 _ _ _ _ _

#print axioms first
#print axioms second
end AspisR1.RPx_InstalledBudget
end
