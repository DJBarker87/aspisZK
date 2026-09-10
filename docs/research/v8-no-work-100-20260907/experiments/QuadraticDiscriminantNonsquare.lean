import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Group.Even
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! Irreducibility of a literal degree-two polynomial supplies the
discriminant nonsquareness needed by the quadratic twist obstruction.
No absence-of-roots or supplied discriminant-nonsquare premise is used.
The fraction-field adapter derives primitivity from irreducibility and
positive degree; the actual multivariate reordering remains explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.QuadraticDiscriminantNonsquare
open Polynomial
noncomputable section

variable {L : Type*} [Field L]

/-- Only three symbolic terms are expanded, never a concrete field domain. -/
theorem quadratic_shape (F : L[X]) (degree : F.natDegree = 2) :
    F = C (F.coeff 2)*X^2 + C (F.coeff 1)*X + C (F.coeff 0) := by
  have finite := F.as_sum_range_C_mul_X_pow' (n := 3) (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, mul_one, pow_one] at finite
  calc
    F = C (F.coeff 0) + C (F.coeff 1)*X + C (F.coeff 2)*X^2 := finite
    _ = C (F.coeff 2)*X^2 + C (F.coeff 1)*X + C (F.coeff 0) := by ac_rfl

/-- A square discriminant constructs a root of this actual polynomial,
contradicting irreducibility and degree two. -/
theorem discriminant_nonsquare [NeZero (2 : L)] (F : L[X])
    (irreducible : Irreducible F) (degree : F.natDegree = 2) :
    ¬ IsSquare (discrim (F.coeff 2) (F.coeff 1) (F.coeff 0)) := by
  intro square
  have leading : F.coeff 2 ≠ 0 := by
    simpa only [Polynomial.leadingCoeff, degree] using
      (Polynomial.leadingCoeff_ne_zero.mpr irreducible.ne_zero)
  obtain ⟨x, equation⟩ := exists_quadratic_eq_zero leading square
  apply irreducible.not_isRoot_of_natDegree_ne_one (by omega) (x := x)
  change F.eval x = 0
  have evaluation := congrArg (fun P : L[X] => P.eval x) (quadratic_shape F degree)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, pow_two] at evaluation
  exact evaluation.trans equation

/-- Nonsquare D excludes a zero square factor and forces d nonsquare.
Thus H nonzero need not be a separate premise at this algebraic step. -/
theorem twist_nonsquare (D d H : L) (nonsquare : ¬ IsSquare D)
    (decomposition : D = d*H^2) : H ≠ 0 ∧ ¬ IsSquare d := by
  constructor
  · intro zero
    apply nonsquare
    rw [decomposition, zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact ⟨0, (zero_mul 0).symm⟩
  · intro square
    apply nonsquare
    rw [decomposition]
    exact square.mul (IsSquare.sq H)

/-- The twist may live in a smaller coefficient field, e.g. K(Z), while
the irreducible quadratic is over K(X,Z). Squares map to squares, so no
unjustified descent or equality of fraction-field presentations is used. -/
theorem irreducible_twist_nonsquare [NeZero (2 : L)]
    {M : Type*} [Field M] (hom : M →+* L) (F : L[X])
    (irreducible : Irreducible F) (degree : F.natDegree = 2)
    (d : M) (H : L)
    (decomposition : discrim (F.coeff 2) (F.coeff 1) (F.coeff 0) = hom d*H^2) :
    H ≠ 0 ∧ ¬ IsSquare d := by
  have inherited := twist_nonsquare _ (hom d) H
    (discriminant_nonsquare F irreducible degree) decomposition
  exact ⟨inherited.1, fun square => inherited.2 (square.map hom)⟩

section FractionField
variable {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
  [Algebra R L] [IsFractionRing R L] [NeZero (2 : L)]

/-- A positive-degree irreducible over a GCD domain is primitive. Gauss's
lemma therefore derives irreducibility over its fraction field, without
monicity or a separately supplied primitive/content premise. -/
theorem fraction_discriminant_nonsquare (F : R[X])
    (irreducible : Irreducible F) (degree : F.natDegree = 2) :
    ¬ IsSquare (algebraMap R L
      (discrim (F.coeff 2) (F.coeff 1) (F.coeff 0))) := by
  have primitive : F.IsPrimitive := irreducible.isPrimitive (by omega)
  have mapped : Irreducible (F.map (algebraMap R L)) :=
    (primitive.irreducible_iff_irreducible_map_fraction_map).mp irreducible
  have mappedDegree : (F.map (algebraMap R L)).natDegree = 2 :=
    (Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective R L) F).trans degree
  have nonsquare := discriminant_nonsquare (F.map (algebraMap R L)) mapped mappedDegree
  simpa only [Polynomial.coeff_map, discrim, map_sub, map_pow, map_mul, map_ofNat]
    using nonsquare

/-- Coefficient-ring decomposition, transported by its literal algebraMap.
This applies after the caller identifies the intended X/Z polynomial order. -/
theorem fraction_twist_nonsquare (F : R[X])
    (irreducible : Irreducible F) (degree : F.natDegree = 2)
    (d H : R)
    (decomposition : discrim (F.coeff 2) (F.coeff 1) (F.coeff 0) = d*H^2) :
    H ≠ 0 ∧ ¬ IsSquare (algebraMap R L d) := by
  have mapped := congrArg (algebraMap R L) decomposition
  simp only [map_mul, map_pow] at mapped
  have inherited := twist_nonsquare _ (algebraMap R L d) (algebraMap R L H)
    (fraction_discriminant_nonsquare (L := L) F irreducible degree) mapped
  refine ⟨?_, inherited.2⟩
  intro zero
  apply inherited.1
  rw [zero, map_zero]
end FractionField

#print axioms quadratic_shape
#print axioms discriminant_nonsquare
#print axioms twist_nonsquare
#print axioms irreducible_twist_nonsquare
#print axioms fraction_discriminant_nonsquare
#print axioms fraction_twist_nonsquare
end
end AspisV8.QuadraticDiscriminantNonsquare
