import XRk_LoopStep
open Aeneas Aeneas.Std Result ControlFlow
namespace XRk_LoopInvariant
/- Partial correctness for finite successful executions of the actual Result
   loop. Failure/divergence are never converted into successful runs. -/
theorem preserve {S V : Type} (body : S → Result (ControlFlow S V))
    (post : V → Prop) (measure : S → Nat)
    (step : ∀ s r,body s=ok r → match r with
      | .done v => post v
      | .cont next => measure next<measure s)
    (s : S) (v : V) (run : loop body s=ok v) : post v := by
  suffices ∀ n s,measure s=n → loop body s=ok v → post v from
    this (measure s) s rfl run
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s size run
    obtain ⟨r,hr,run⟩ := XRk_LoopStep.unroll body s v run
    have localStep := step s r hr
    cases r with
    | done out =>
      have same := Result.ok.inj run
      subst out
      exact localStep
    | cont next => exact ih (measure next) (by omega) next rfl run
#print axioms preserve
end XRk_LoopInvariant
