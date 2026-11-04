import PV_B3P_CounterGuards571227
namespace PV_B3P_IndexCounter579227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Exact scalar update in IndexRange::next_unchecked, before the callback.
The terminating branch leaves start unchanged and never invokes the callback. -/
def advance (length current : Usize) : Usize :=
  if current = length then current else Usize.wrapping_add current 1#usize

def sourceState : Nat → Usize → Usize
  | 0, _ => 0#usize
  | n+1, length => advance length (sourceState n length)

theorem state_ordered (n : Nat) (length : Usize) :
    (sourceState n length).val ≤ length.val := by
  induction n with
  | zero => change (0#usize).val ≤ length.val; scalar_tac
  | succ n ih =>
    by_cases done : sourceState n length = length
    · simp only [sourceState,advance,if_pos done,done]
    · have safe := PV_B3P_PreconditionFormatting569227.index_range_conditions
        (sourceState n length) length ih done
      simpa only [sourceState,advance,if_neg done] using safe.2.2

def orderedCondition (n : Nat) (length : Usize) : Bool :=
  decide ((sourceState n length).val ≤ length.val)

theorem ordered_guard (n : Nat) (length : Usize) : orderedCondition n length = true :=
  decide_eq_true (state_ordered n length)

/-- Current start is snapshotted BEFORE the private increment, exactly as the
source argument handed to the element-reading callback. The callback's data
metadata is the constructor's same length; native pointer realization is not
part of this numeric observer. -/
def indexEvent (n : Nat) (length : Usize) : Option IndexState :=
  if sourceState n length = length then none
  else some ⟨(sourceState n length).val,length.val⟩

theorem index_guard (n : Nat) (length : Usize) (observed : IndexState)
    (ran : indexEvent n length = some observed) : indexGuard observed := by
  by_cases done : sourceState n length = length
  · simp only [indexEvent,if_pos done] at ran
    cases ran
  · simp only [indexEvent,if_neg done] at ran
    cases ran
    exact (PV_B3P_PreconditionFormatting569227.index_range_conditions
      (sourceState n length) length (state_ordered n length) done).1

def addEvent (n : Nat) (length : Usize) (checks : Bool) : Option ArithmeticState :=
  if sourceState n length = length then none
  else if checks then some (.add (sourceState n length).val 1 (UScalar.max .Usize)) else none

theorem add_guard (n : Nat) (length : Usize) (checks : Bool) (observed : ArithmeticState)
    (ran : addEvent n length checks = some observed) : arithmeticGuard observed := by
  by_cases done : sourceState n length = length
  · simp only [addEvent,if_pos done] at ran
    cases ran
  · cases checks with
    | false => simp only [addEvent,if_neg done,Bool.false_eq_true,if_false] at ran; cases ran
    | true =>
      simp only [addEvent,if_neg done,if_true] at ran
      cases ran
      exact (PV_B3P_PreconditionFormatting569227.index_range_conditions
        (sourceState n length) length (state_ordered n length) done).2.1

theorem ordered_certificate {α : Type} (n : Nat) (length : Usize)
    (normal first second : Result α) :
    ¬ diagnostic (orderedCondition n length = true) ∧
      branch (orderedCondition n length = true) normal first = branch (orderedCondition n length = true) normal second :=
  (assertion (orderedCondition n length) true normal first second).2 (ordered_guard n length)

theorem index_certificate {α : Type} (n : Nat) (length : Usize) (observed : IndexState)
    (ran : indexEvent n length = some observed) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  (index_out_of_bounds observed normal first second).2 (index_guard n length observed ran)

theorem callback_assertion_certificate {α : Type} (n : Nat) (length : Usize) (observed : IndexState)
    (ran : indexEvent n length = some observed) (normal first second : Result α) :
    ¬ diagnostic (decide (indexGuard observed) = true) ∧
      branch (decide (indexGuard observed) = true) normal first =
        branch (decide (indexGuard observed) = true) normal second :=
  (assertion (decide (indexGuard observed)) true normal first second).2
    (decide_eq_true (index_guard n length observed ran))

theorem add_certificate {α : Type} (n : Nat) (length : Usize) (checks : Bool) (observed : ArithmeticState)
    (ran : addEvent n length checks = some observed) (normal first second : Result α) :
    ¬ diagnostic (arithmeticGuard observed) ∧
      branch (arithmeticGuard observed) normal first = branch (arithmeticGuard observed) normal second :=
  (arithmetic_overflow observed normal first second).2 (add_guard n length checks observed ran)
#print axioms state_ordered
#print axioms ordered_guard
#print axioms index_guard
#print axioms add_guard
#print axioms ordered_certificate
#print axioms index_certificate
#print axioms callback_assertion_certificate
#print axioms add_certificate
end PV_B3P_IndexCounter579227
