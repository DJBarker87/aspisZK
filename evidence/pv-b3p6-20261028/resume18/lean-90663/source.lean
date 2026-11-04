import PV_B3P_PanicPatterns571227
namespace PV_B3P_StepPanic587227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Actual 224 ->96 ->439 scalar step; zero branch is the only path to26460. -/
def sourceCondition : Bool := decide (Nat.succ 3 ≠ 0)
theorem certificate {α : Type} (normal first second : Result α) :
    ¬ diagnostic (sourceCondition = true) ∧
      branch (sourceCondition = true) normal first = branch (sourceCondition = true) normal second :=
  (explicit_panic sourceCondition normal first second).2 (decide_eq_true (Nat.succ_ne_zero 3))
#print axioms certificate
end PV_B3P_StepPanic587227
