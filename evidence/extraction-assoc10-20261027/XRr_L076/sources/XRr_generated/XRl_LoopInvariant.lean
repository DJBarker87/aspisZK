import XRk_LoopStep
open Aeneas Aeneas.Std Result ControlFlow
namespace XRl_LoopInvariant
/-- Partial correctness of the actual Result loop with an evolving invariant.
This augments XRk's postcondition lemma; it does not replace its loop semantics. -/
theorem preserve {S V : Type} (body : S → Result (ControlFlow S V))
    (invariant : S → Prop) (post : V → Prop) (measure : S → Nat)
    (step : ∀ s r, invariant s → body s=ok r → match r with
      | .done v => post v
      | .cont next => invariant next ∧ measure next<measure s)
    (s : S) (v : V) (initial : invariant s) (run : loop body s=ok v) : post v := by
  suffices ∀ n s,measure s=n → invariant s → loop body s=ok v → post v from
    this (measure s) s rfl initial run
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s size inv run
    obtain ⟨r,hr,run⟩ := XRk_LoopStep.unroll body s v run
    have localStep := step s r inv hr
    cases r with
    | done out =>
      have same := Result.ok.inj run
      subst out
      exact localStep
    | cont next => exact ih (measure next) (by omega) next rfl localStep.1 run
#print axioms preserve
end XRl_LoopInvariant
