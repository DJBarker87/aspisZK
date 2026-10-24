import S1NativeCompactModelV1
set_option autoImplicit false
namespace AspisS1LoopSafety
open Aeneas Aeneas.Std Result

/-- Accepted-result invariant transport through the actual emitted Std.loop.
Unlike a total Hoare spec, failures and divergence are allowed; neither is
silently assumed away. The body must preserve the invariant on its own
successful continuation and the postcondition on its own successful exit. -/
theorem accepted {α β : Type} (body : α → Result (ControlFlow α β))
    (inv : α → Prop) (post : β → Prop)
    (step : ∀ x, inv x → ∀ r, body x=ok r →
      match r with | .cont next => inv next | .done value => post value)
    (x : α) (initial : inv x) (y : β) (success : loop body x=ok y) : post y := by
  have all : ∀ x, inv x → ∀ y, loop body x=ok y → post y := by
    apply loop.fixpoint_induct body
      (fun f => ∀ x, inv x → ∀ y, f x=ok y → post y)
    · apply Lean.Order.admissible_pi_apply (fun x (r : Result β) =>
        inv x → ∀ y, r=ok y → post y)
      intro x
      apply Lean.Order.admissible_flatOrder
      intro _ y impossible
      cases impossible
    · intro recur ih x hx y h
      cases call : body x with
      | fail error => simp only [call] at h; cases h
      | div => simp only [call] at h; cases h
      | ok r =>
        simp only [call] at h
        cases r with
        | cont next => exact ih next (step x hx (.cont next) call) y h
        | done value =>
          have same : value=y := Result.ok.inj h
          subst value
          exact step x hx (.done y) call
  exact all x initial y success

#print axioms accepted
end AspisS1LoopSafety
