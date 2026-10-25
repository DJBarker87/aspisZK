import RawJ_OuterBudget
import GExq_OuterRecord
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_RecordedBudget
open Aeneas Aeneas.Std Result S2W_Trace GExq_OuterLower RawJ_OuterBudget

theorem count {A : Type} (impl : {B : Type} → Call B → Oracle B)
    (law : ∀ {B : Type} (op : Call B), GExp_CountLaws.count (cost op) (impl op))
    (p : Code A) (n : Nat) (h : bounded n p) (before : List GExq_OuterRecord.Event) :
    GExp_CountLaws.count n (GExq_OuterRecord.record impl p before) := by
  induction p generalizing n before with
  | done a => exact GExp_CountLaws.pure_count _ _
  | step r k ih => cases r with
    | ok a => exact ih a n h before
    | fail e => exact GExp_CountLaws.lift_count _ (.fail e)
    | div => exact GExp_CountLaws.lift_count _ .div
  | call op k ih =>
    exact GExp_CountLaws.then_count h.1 (law op)
      (fun a => ih a (n-cost op) (h.2 a) (before ++ GExq_OuterRecord.project op a))

#print axioms count
end AspisR1.RawJ_RecordedBudget
end
