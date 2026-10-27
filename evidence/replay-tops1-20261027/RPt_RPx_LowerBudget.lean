import RPt_RPx_OuterCredit
import RPz7_GExq_FirstBudget
import RPz7_GExq_SecondBudget
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

#print axioms lower
end AspisR1.RPx_LowerBudget
end
