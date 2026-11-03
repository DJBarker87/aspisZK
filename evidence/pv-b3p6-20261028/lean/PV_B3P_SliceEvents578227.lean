import PV_B3P_CounterGuards571227
namespace PV_B3P_SliceEvents578227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- The encoded end value is the actual scalar read by the ZST branch.
No equation relating it to a valid native pointer or slice length is assumed.
The observation is BEFORE unchecked_sub's precondition call. -/
def sourceEvent (zeroSized checks : Bool) (encodedEnd : Usize) : Option ArithmeticState :=
  if zeroSized then
    if encodedEnd = 0#usize then none
    else if checks then some (.sub encodedEnd.val 1) else none
  else none

theorem event_guard (zeroSized checks : Bool) (encodedEnd : Usize)
    (observed : ArithmeticState) (ran : sourceEvent zeroSized checks encodedEnd = some observed) :
    arithmeticGuard observed := by
  cases zeroSized <;> cases checks <;>
    simp only [sourceEvent, Bool.false_eq_true, if_false, if_true] at ran
  all_goals try { cases ran }
  by_cases empty : encodedEnd = 0#usize
  · simp only [if_pos empty] at ran
    cases ran
  · simp only [if_neg empty] at ran
    cases ran
    exact PV_B3P_CounterGuards571227.subtraction_guard encodedEnd empty

theorem event_certificate {α : Type} (zeroSized checks : Bool) (encodedEnd : Usize)
    (observed : ArithmeticState) (ran : sourceEvent zeroSized checks encodedEnd = some observed)
    (normal first second : Result α) :
    ¬ diagnostic (arithmeticGuard observed) ∧
      branch (arithmeticGuard observed) normal first = branch (arithmeticGuard observed) normal second :=
  (arithmetic_overflow observed normal first second).2 (event_guard zeroSized checks encodedEnd observed ran)
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_SliceEvents578227
