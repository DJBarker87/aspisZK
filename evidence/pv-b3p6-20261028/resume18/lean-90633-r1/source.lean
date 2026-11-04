import PV_B3P_IndexCounter579227
namespace PV_B3P_IndexCursorFamily579227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_IndexCounter579227
set_option autoImplicit false
/-- Actual constructor/caller chain18/44/45/207/329, instruction9851. -/
theorem certificate_207_9851 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (orderedCondition 0 3#usize = true) ∧
      branch (orderedCondition 0 3#usize = true) normal first = branch (orderedCondition 0 3#usize = true) normal second :=
  ordered_certificate 0 3#usize normal first second
#print axioms certificate_207_9851
/-- Actual constructor/caller chain18/44/45/207/329, instruction9856. -/
theorem certificate_207_9856 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (orderedCondition 0 3#usize = true) ∧
      branch (orderedCondition 0 3#usize = true) normal first = branch (orderedCondition 0 3#usize = true) normal second :=
  ordered_certificate 0 3#usize normal first second
#print axioms certificate_207_9856
/-- Actual constructor/caller chain18/44/45/207/329, instruction9882. -/
theorem certificate_207_9882 {α : Type} (n : Nat) (checks : Bool) (observed : ArithmeticState)
    (ran : addEvent n 3#usize checks = some observed) (normal first second : Result α) :
    ¬ diagnostic (arithmeticGuard observed) ∧
      branch (arithmeticGuard observed) normal first = branch (arithmeticGuard observed) normal second :=
  add_certificate n 3#usize checks observed ran normal first second
#print axioms certificate_207_9882
/-- Actual constructor/caller chain18/44/45/207/329, instruction23398. -/
theorem certificate_329_23398 {α : Type} (n : Nat) (observed : IndexState)
    (ran : indexEvent n 3#usize = some observed) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  index_certificate n 3#usize observed ran normal first second
#print axioms certificate_329_23398
/-- Actual constructor/caller chain18/44/45/207/329, instruction30694. -/
theorem certificate_329_30694 {α : Type} (n : Nat) (observed : IndexState)
    (ran : indexEvent n 3#usize = some observed) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  index_certificate n 3#usize observed ran normal first second
#print axioms certificate_329_30694
/-- Actual constructor/caller chain18/44/45/207/329, instruction23409. -/
theorem certificate_329_23409 {α : Type} (n : Nat) (observed : IndexState)
    (ran : indexEvent n 3#usize = some observed) (normal first second : Result α) :
    ¬ diagnostic (decide (indexGuard observed) = true) ∧
      branch (decide (indexGuard observed) = true) normal first = branch (decide (indexGuard observed) = true) normal second :=
  callback_assertion_certificate n 3#usize observed ran normal first second
#print axioms certificate_329_23409
end PV_B3P_IndexCursorFamily579227
