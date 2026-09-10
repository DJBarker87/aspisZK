import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Group.Even
import Mathlib.RingTheory.Localization.FractionRing

/-! A nonsquare twist cannot acquire a polynomial square after multiplying
by a nonzero square. The OOD obstruction is an actual fixed coefficient of
H, with outer Z and inner X. The factor decomposition and its nonsquare
property are explicit prerequisites, not conclusions of this ingredient. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.QuadraticTwistObstruction
open Polynomial
noncomputable section

theorem nonsquare_twist_forces_zero {L : Type*} [Field L] (d A H : L)
    (nonsquare : ¬ IsSquare d) (identity : A^2 = d*H^2) : H = 0 := by
  by_contra nonzero
  apply nonsquare
  apply (isSquare_iff_exists_sq d).mpr
  refine ⟨A/H, ?_⟩
  rw [div_pow, identity]
  exact (mul_div_cancel_right₀ d (pow_ne_zero 2 nonzero)).symm

variable {K : Type*} [Field K]

/-- Nonsquareness is in K(Z), not merely absence of a polynomial square
root in K[Z]. The injection back into K[Z] is derived from the fraction ring. -/
theorem polynomial_twist_forces_zero (d A H : K[X])
    (nonsquare : ¬ IsSquare (algebraMap K[X] (FractionRing K[X]) d))
    (identity : A^2 = d*H^2) : H = 0 := by
  have mapped := congrArg (algebraMap K[X] (FractionRing K[X])) identity
  simp only [map_pow, map_mul] at mapped
  have vanishing := nonsquare_twist_forces_zero
    (algebraMap K[X] (FractionRing K[X]) d)
    (algebraMap K[X] (FractionRing K[X]) A)
    (algebraMap K[X] (FractionRing K[X]) H) nonsquare mapped
  exact (IsFractionRing.injective K[X] (FractionRing K[X]))
    (vanishing.trans (map_zero (algebraMap K[X] (FractionRing K[X]))).symm)

/-- H is K[X][Z]. Evaluate its INNER X variable at t, leaving Z symbolic. -/
def atPoint (H : Polynomial K[X]) (t : K) : K[X] :=
  H.map (Polynomial.evalRingHom t)

/-- This coefficient test is independent of the nonsquare-twist premise.
It also applies with X/Z roles exchanged, using the explicitly reordered
input polynomial rather than silently swapping evaluations. -/
theorem atPoint_zero_iff (H : Polynomial K[X]) (t : K) :
    atPoint H t = 0 ↔ ∀ j, (H.coeff j).eval t = 0 := by
  constructor
  · intro zero j
    have coefficient := congrArg (fun P : K[X] => P.coeff j) zero
    simpa only [atPoint, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
      Polynomial.coeff_zero] using coefficient
  · intro coefficients
    apply Polynomial.ext
    intro j
    simpa only [atPoint, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
      Polynomial.coeff_zero] using coefficients j

/-- Each coefficient at its ORIGINAL Z index vanishes. No assertion that
the leading degree survives specialization is required or used. -/
theorem identity_all_coefficients_zero (d : K[X]) (H : Polynomial K[X])
    (nonsquare : ¬ IsSquare (algebraMap K[X] (FractionRing K[X]) d))
    (t : K) (answer : K[X]) (identity : answer^2 = d*(atPoint H t)^2) :
    ∀ j, (H.coeff j).eval t = 0 := by
  exact (atPoint_zero_iff H t).mp
    (polynomial_twist_forces_zero d answer (atPoint H t) nonsquare identity)

/-- This is the leading Z coefficient, a polynomial in X, chosen from H
alone before either OOD point or answer. It is not the leading coefficient
of H(t,Z), whose degree can drop. -/
def obstruction (H : Polynomial K[X]) : K[X] := H.leadingCoeff

theorem obstruction_nonzero (H : Polynomial K[X]) (nonzero : H ≠ 0) :
    obstruction H ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr nonzero

theorem obstruction_degree (H : Polynomial K[X]) (bound : Nat)
    (coefficients : ∀ j, (H.coeff j).natDegree ≤ bound) :
    (obstruction H).natDegree ≤ bound := coefficients H.natDegree

/-- A vanishing whole specialization forces the constructed coefficient
obstruction, without a twist, root, primitivity or degree-preservation premise. -/
theorem specialization_obstruction_zero (H : Polynomial K[X]) (t : K)
    (zero : atPoint H t = 0) : (obstruction H).eval t = 0 :=
  (atPoint_zero_iff H t).mp zero H.natDegree

theorem identity_obstruction_zero (d : K[X]) (H : Polynomial K[X])
    (nonsquare : ¬ IsSquare (algebraMap K[X] (FractionRing K[X]) d))
    (t : K) (answer : K[X]) (identity : answer^2 = d*(atPoint H t)^2) :
    (obstruction H).eval t = 0 :=
  identity_all_coefficients_zero d H nonsquare t answer identity H.natDegree

/-- One nonzero obstruction is constructed before the two points. Each
answer may depend arbitrarily on its available OOD prefix. This is an
algebraic pair implication, not an independent-uniform sampler theorem. -/
theorem exists_fixed_obstruction (d : K[X]) (H : Polynomial K[X])
    (nonzero : H ≠ 0)
    (nonsquare : ¬ IsSquare (algebraMap K[X] (FractionRing K[X]) d))
    (bound : Nat) (coefficients : ∀ j, (H.coeff j).natDegree ≤ bound) :
    ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ bound ∧ E = H.leadingCoeff ∧
      ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X]),
        (∀ r, (answers r)^2 = d*(atPoint H (points r))^2) →
        ∀ r, E.eval (points r) = 0 := by
  refine ⟨obstruction H, obstruction_nonzero H nonzero,
    obstruction_degree H bound coefficients, rfl, ?_⟩
  intro points answers identities r
  exact identity_obstruction_zero d H nonsquare (points r) (answers r) (identities r)

#print axioms nonsquare_twist_forces_zero
#print axioms polynomial_twist_forces_zero
#print axioms atPoint_zero_iff
#print axioms identity_all_coefficients_zero
#print axioms obstruction_nonzero
#print axioms obstruction_degree
#print axioms specialization_obstruction_zero
#print axioms identity_obstruction_zero
#print axioms exists_fixed_obstruction
end
end AspisV8.QuadraticTwistObstruction
