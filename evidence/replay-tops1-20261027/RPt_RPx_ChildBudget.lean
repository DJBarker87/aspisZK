import RPt_RPx_LowerBudget
import RPt_RPx_GenericSecond
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_ChildBudget
open Aeneas Aeneas.Std Result S2W_Trace RPx_OuterCredit
open GExq_OuterLower GExp_CountLaws
attribute [local irreducible] count GExq_FirstCode.code GExq_SecondCode.code

theorem children {F C A : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (op : Call A) :
    count (charge op) (GExq_ChildCode.execute adapter ops stage finish reserved query geo B std hashv op) := by
  cases op <;> simp only [GExq_ChildCode.execute,charge]
  all_goals try exact lift_count _ _
  · apply then_count (Nat.le_refl 1018)
    · exact RPx_GenericFirst.first _ _ _ _ _ _ _ _ _ _
    · intro r;exact pure_count _ _
  · exact RPx_GenericSecond.second _ _ _ _ _ _ _ _

#print axioms children
end AspisR1.RPx_ChildBudget
end
