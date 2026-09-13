import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace AspisV8R12
open Polynomial
variable {K : Type*} [CommRing K]

noncomputable def boundaryOperator (h : K[X]) : K[X] :=
  (1 - X) * h - X * h.comp (X - 1)
noncomputable def polynomialBoundary (q : K[X]) : K := q.eval 0 + q.eval 1
theorem boundaryOperator_zero : boundaryOperator (0 : K[X]) = 0 := by simp [boundaryOperator]
theorem boundaryOperator_add (h k : K[X]) :
    boundaryOperator (h + k) = boundaryOperator h + boundaryOperator k := by
  simp only [boundaryOperator, add_comp]; ring
theorem boundaryOperator_sub (h k : K[X]) :
    boundaryOperator (h - k) = boundaryOperator h - boundaryOperator k := by
  simp only [boundaryOperator, sub_comp]; ring
theorem boundaryOperator_boundary (h : K[X]) : polynomialBoundary (boundaryOperator h) = 0 := by
  simp [polynomialBoundary, boundaryOperator, eval_comp]
theorem boundaryOperator_eval (h : K[X]) (x : K) :
    (boundaryOperator h).eval x = (1-x) * h.eval x - x * h.eval (x-1) := by
  simp [boundaryOperator, eval_comp]
#print axioms boundaryOperator_add
#print axioms boundaryOperator_boundary
#print axioms boundaryOperator_eval
end AspisV8R12
