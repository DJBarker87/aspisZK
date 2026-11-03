import PV_B3P_StepExpect571227
namespace PV_B3P_StepSource572227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Source observation immediately after the guarded forward_checked call.
The outer Option records whether that source instruction was executed. The
inner Option is its actual return value, before expect inspects its tag. -/
def event (item finish : Usize) : Result (Option (Option Usize)) :=
  if item.val < finish.val then do
    let answer ← core.iter.range.StepUsize.forward_checked item 1#usize
    .ok (some answer)
  else .ok none

/-- Every observed source event has a Some successor. This proves the input
of expect, rather than deriving panic absence from a whole-function Result. -/
theorem event_guard (item finish : Usize) (answer : Option Usize)
    (observed : event item finish = .ok (some answer)) : optionGuard answer := by
  by_cases active : item.val < finish.val
  · obtain ⟨next,run,_⟩ := PV_B3P_NthFinalGuard559227.increment_some item finish active
    have same : answer = some next := by
      have equal : Result.ok (some answer) = .ok (some (some next)) :=
        observed.symm.trans (by simp only [event, if_pos active, run, bind_tc_ok])
      cases equal
      rfl
    rw [same]
    rfl
  · simp only [event,if_neg active] at observed
    cases observed

/-- All current scalar states of the default iterator bodies are included;
no range-entry, callback-success or resource-adequacy premise is introduced. -/
theorem event_certificate {α : Type} (item finish : Usize) (answer : Option Usize)
    (observed : event item finish = .ok (some answer))
    (normal first second : Result α) :
    ¬ diagnostic (optionGuard answer) ∧
      branch (optionGuard answer) normal first = branch (optionGuard answer) normal second :=
  (unwrap_expect answer normal first second).2 (event_guard item finish answer observed)
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_StepSource572227
