import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Derivative

/-! Two polynomial roots with the same value at a simple evaluation point
are equal. This is a deterministic rigidity statement, not a bound on the
number of challenges with roots or a component-curve recovery theorem. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.SimplePolynomialRootRigidity
open Polynomial
variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]

theorem eval_hom_eq_of_image_eq (hom : R →+* S) (P : R[X]) (u v : R)
    (same : hom u = hom v) : hom (P.eval u) = hom (P.eval v) := by
  rw [← Polynomial.eval₂_at_apply hom u, ← Polynomial.eval₂_at_apply hom v, same]

/-- No primeness, degree or monicity premise is required. Simplicity is
tested after the actual coefficient homomorphism, not assumed generically. -/
theorem roots_equal (hom : R →+* S) (P : R[X]) (u v : R)
    (leftRoot : P.eval u = 0) (rightRoot : P.eval v = 0)
    (same : hom u = hom v) (simple : hom (P.derivative.eval u) ≠ 0) : u = v := by
  have divides : X - C u ∣ P := Polynomial.dvd_iff_isRoot.mpr leftRoot
  obtain ⟨H, product⟩ := divides
  by_contra different
  have difference : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm different)
  have cofactorRoot : H.eval v = 0 := by
    have productRoot := rightRoot
    rw [product, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at productRoot
    exact (mul_eq_zero.mp productRoot).resolve_left difference
  have derivative : P.derivative.eval u = H.eval u := by
    rw [product, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_one, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    simp only [one_mul, sub_self, zero_mul, add_zero]
  apply simple
  rw [derivative, eval_hom_eq_of_image_eq hom H u v same, cofactorRoot, map_zero]

/-- Here the coefficient ring is K[X], and the outer polynomial variable
is Y. U and V may have been chosen after any later protocol challenge. -/
theorem polynomial_roots_equal {K : Type*} [Field K]
    (F : Polynomial K[X]) (t : K) (U V : K[X])
    (leftRoot : F.eval U = 0) (rightRoot : F.eval V = 0)
    (same : U.eval t = V.eval t)
    (simple : (F.derivative.eval U).eval t ≠ 0) : U = V :=
  roots_equal (Polynomial.evalRingHom t) F U V leftRoot rightRoot same simple

#print axioms eval_hom_eq_of_image_eq
#print axioms roots_equal
#print axioms polynomial_roots_equal
end AspisV8.SimplePolynomialRootRigidity
