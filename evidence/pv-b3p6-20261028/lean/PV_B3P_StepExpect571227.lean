import PV_B3P_PanicPatterns571227
namespace PV_B3P_StepExpect571227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- Numeric observation at the default range/inclusive range checked-successor
operation. Every captured expect has this guarded shape; exhaustion and early
return can only prevent this operation. No callback or formatter is run here. -/
def checked_diagnostic (item finish : Usize) : Result Bool :=
  if item.val < finish.val then do
    let answer ← core.iter.range.StepUsize.forward_checked item 1#usize
    .ok answer.isNone
  else .ok false

/-- G holds for every checked-successor state, with no range-entry invariant:
strict order alone forces forward_checked(1) to return Some. -/
theorem checked_guard (item finish : Usize) (active : item.val < finish.val) :
    ∃ answer, core.iter.range.StepUsize.forward_checked item 1#usize = .ok answer ∧
      optionGuard answer := by
  obtain ⟨next,run,_⟩ := PV_B3P_NthFinalGuard559227.increment_some item finish active
  exact ⟨some next,run,rfl⟩

/-- The diagnostic observation is false for ALL counter pairs, including
reversed and maximal scalar endpoints. This is a numeric local source law;
carrier, specialization, source-event and caller bindings are not implied. -/
theorem all_states (item finish : Usize) : checked_diagnostic item finish = .ok false := by
  by_cases active : item.val < finish.val
  · obtain ⟨next,run,_⟩ := PV_B3P_NthFinalGuard559227.increment_some item finish active
    simp only [checked_diagnostic,if_pos active,run,bind_tc_ok,Option.isNone_some]
  · simp only [checked_diagnostic,if_neg active]

/-- Generic pattern lemma applied once to the full checked-successor family. -/
theorem handler_independent {α : Type} (item finish : Usize)
    (active : item.val < finish.val) (answer : Option Usize)
    (returned : core.iter.range.StepUsize.forward_checked item 1#usize = .ok answer)
    (normal first second : Result α) :
    ¬ diagnostic (optionGuard answer) ∧
      branch (optionGuard answer) normal first = branch (optionGuard answer) normal second := by
  obtain ⟨next,run,_⟩ := PV_B3P_NthFinalGuard559227.increment_some item finish active
  have equal : answer = some next := by
    have result := returned.symm.trans run
    cases result
    rfl
  subst answer
  exact (unwrap_expect (some next) normal first second).2 rfl

#print axioms checked_guard
#print axioms all_states
#print axioms handler_independent
end PV_B3P_StepExpect571227
