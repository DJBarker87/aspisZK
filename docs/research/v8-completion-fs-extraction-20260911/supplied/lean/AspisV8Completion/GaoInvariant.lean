/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.GaoInvariant
variable {F : Type*} [Field F]
open Polynomial

/-- Extended Euclid preserves the exact Bezout equation. The loop's degree
stopping argument, runtime and selected circle transform remain obligations. -/
theorem bezout_step (G R r0 r1 u0 u1 v0 v1 quotient : F[X])
    (h0 : r0=u0*G+v0*R) (h1 : r1=u1*G+v1*R) :
    r0-quotient*r1 = (u0-quotient*u1)*G+(v0-quotient*v1)*R := by
  rw [h0,h1]
  ring

/-- The candidate agrees with each sample outside locator roots. This is
actual algebra, not a record carrying the desired decoder conclusion. -/
theorem candidate_at_sample (G R Q E U candidate : F[X]) (x y : F)
    (vanishes : G.eval x=0) (interpolates : R.eval x=y)
    (bezout : Q=U*G+E*R) (division : Q=E*candidate)
    (notError : E.eval x≠0) : candidate.eval x=y := by
  have equality : E.eval x*candidate.eval x=E.eval x*y := by
    calc
      E.eval x*candidate.eval x = Q.eval x := by rw [division, Polynomial.eval_mul]
      _ = E.eval x*y := by rw [bezout]; simp [vanishes,interpolates]
  exact mul_left_cancel₀ notError equality

#print axioms bezout_step
#print axioms candidate_at_sample
end AspisV8Completion.GaoInvariant
