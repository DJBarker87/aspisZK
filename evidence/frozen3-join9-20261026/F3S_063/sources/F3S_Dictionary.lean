import F3S_NativeChildren
import SdkD_PairBatches
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_Dictionary
open Aeneas Aeneas.Std Result
 theorem sdk {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    GExq_Caller.sdk adapter ops stage finish reserved query geo B std=
      SdkD_PairBatches.dictionary adapter ops stage finish reserved query geo B std := by
  rfl
 theorem first {C : Type} (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    GExp_FirstCode.installed (GExp_FirstPair.base ops reserved query geo) B std=
      Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved query geo B std := by
  rw [GExp_FirstPair.installed,Uni_Install.compose_tx1]
  rfl
 theorem second {F C : Type} (stage : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C) :
    let base := GExq_SecondCode.installed (GExp_SecondPair.base stage finish reserved query geo) reserved
    base.op15=ok 7751#usize ∧ base.op14=ok 7783#usize ∧
      ∀ root,base.unwrap32 (.Ok root)=ok root := by
  exact ⟨rfl,rfl,fun root=>rfl⟩
#print axioms sdk
#print axioms first
#print axioms second
end AspisR1.F3S_Dictionary
end
