import Aeneas

/-! Success invariants for the existing partial-fixpoint loop. Failed and
divergent executions are retained; this lemma asserts no termination premise.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsLoopInvariant
open Aeneas Aeneas.Std Result ControlFlow

theorem success {A B : Type} (body : A → Result (ControlFlow A B))
    (inv : A → Prop) (post : B → Prop)
    (hbody : ∀ x,inv x → ∀ r,body x = .ok r →
      match r with
      | .cont next => inv next
      | .done out => post out) :
    ∀ x,inv x → ∀ out,loop body x = .ok out → post out := by
  apply loop.fixpoint_induct (body:=body)
    (motive:=fun f => ∀ x,inv x → ∀ out,f x = .ok out → post out)
  · apply Lean.Order.admissible_pi
    intro x
    apply Lean.Order.admissible_pi
    intro hx
    apply Lean.Order.admissible_apply
      (fun (_ : A) (r : Result B) => ∀ out,r = .ok out → post out) x
    apply Lean.Order.admissible_flatOrder
    intro out h
    cases h
  · intro f ih x hx out hrun
    cases hb : body x with
    | fail error => simp only [hb] at hrun;cases hrun
    | div => simp only [hb] at hrun;cases hrun
    | ok control =>
      cases control with
      | done value =>
        simp only [hb] at hrun
        have heq := Result.ok.inj hrun
        exact heq ▸ hbody x hx (.done value) hb
      | cont next =>
        simp only [hb] at hrun
        exact ih next (hbody x hx (.cont next) hb) out hrun

#print axioms success
end AspisR1.CuSavingsLoopInvariant
