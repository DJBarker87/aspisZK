import F3S_NativeChildren
import AuS1_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_SdkDictionary
open Aeneas Aeneas.Std Result
 theorem sdk {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    GExq_Caller.sdk adapter ops (AuS1_Install.base stage) finish reserved query geo B std=
      SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std := by
  rw [AuS1_Install.dictionary]
  rfl
#print axioms sdk
end AspisR1.F3S_SdkDictionary
end
