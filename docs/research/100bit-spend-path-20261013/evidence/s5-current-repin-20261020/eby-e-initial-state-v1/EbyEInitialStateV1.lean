import AspisR1EbyEFourDotSourceStepV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1EbyEInitialStateV1

open AspisR1EbyEFourDotSourceStepV1

def sourceDotNew : Result Dot := do
  let a := Array.repeat 4#usize 0#u64
  ok { sums := a }

def sourceEbyENew : Result State := do
  let d ← sourceDotNew
  ok { ac := d, bd := d, ad := d, bc := d, count := 0#usize }

theorem sourceNew_success_initial_bound (s : State)
    (h : sourceEbyENew = .ok s) :
    s.count.val = 0 ∧ Bounded 0 s := by
  simp [sourceEbyENew, sourceDotNew] at h
  subst s
  constructor
  · rfl
  · simp only [AspisR1EbyEFourDotSourceStepV1.Bounded]
    repeat' constructor
    all_goals
      unfold AspisR1FinishDotCountBoundV2.sumsBelowCount
      intro j hj
      have hjCases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hjCases with h | h | h | h
      · subst j; simp [Array.repeat]
      · subst j; simp [Array.repeat]
      · subst j; simp [Array.repeat]
      · subst j; simp [Array.repeat]

#print axioms sourceNew_success_initial_bound

end AspisR1EbyEInitialStateV1
