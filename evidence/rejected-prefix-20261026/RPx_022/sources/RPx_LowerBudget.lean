import RPx_OuterCredit
import GExq_FirstBudget
import GExq_SecondBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_LowerBudget
open Aeneas Aeneas.Std Result S2W_Trace RPx_OuterCredit
open GExq_OuterLower GExp_CountLaws

theorem lower {A : Type} (impl : {B : Type} → Call B → Oracle B)
    (children : ∀ {B : Type} (op : Call B),count (charge op) (impl op))
    (p : Code A) (n : Nat) (credit : Credit p n) : count n (GExq_OuterLower.lower impl p) := by
  induction p generalizing n with
  | done a => exact pure_count _ _
  | step r k ih => cases r with
    | ok a => exact ih a n credit
    | fail e => exact fun _=>Nat.zero_le _
    | div => exact fun _=>Nat.zero_le _
  | call op k ih =>
    exact then_count credit.1 (children op) (fun a=>ih a (n-charge op) (credit.2 a))

theorem children {F C A : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (op : Call A) :
    count (charge op) (GExq_ChildCode.execute adapter ops stage finish reserved query geo B std hashv op) := by
  cases op <;> simp only [GExq_ChildCode.execute,charge]
  all_goals try exact lift_count _ _
  · apply then_count (Nat.le_refl 1018)
    · exact GExq_FirstBudget.first _ _ _ _ _ _ _ _ _
    · intro r;exact pure_count _ _
  · exact GExq_SecondBudget.second _ _ _ _ _ _ _

#print axioms lower
#print axioms children
end AspisR1.RPx_LowerBudget
end
