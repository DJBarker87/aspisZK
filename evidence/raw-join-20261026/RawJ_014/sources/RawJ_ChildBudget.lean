import RawJ_FirstBudget
import RawJ_SecondBudget
import RawJ_OuterBudget
import GExq_ChildCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_ChildBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_CountLaws

theorem child {F C A : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (op : S2W_Trace.Call A) :
    count (RawJ_OuterBudget.cost op)
      (GExq_ChildCode.execute adapter ops stage finish reserved query geo B std hashv op) := by
  cases op <;> simp only [GExq_ChildCode.execute,RawJ_OuterBudget.cost]
  all_goals try exact lift_count _ _
  · apply then_count (cost:=1018)
    · omega
    · exact RawJ_FirstBudget.first _ _ _ _ _ _ _ _ _ _
    · intro r
      exact pure_count _ _
  · exact RawJ_SecondBudget.second _ _ _ _ _ _ _ _ _

#print axioms child
end AspisR1.RawJ_ChildBudget
end
