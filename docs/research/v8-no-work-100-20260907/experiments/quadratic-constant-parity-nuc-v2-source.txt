import QuadraticDiscriminantNonsquare
import QuadraticTwistObstruction
import PolynomialParityLocalization
import FactorCoherence

/-! Constant-X parity for an actual quadratic factor. The OOD root
identities imply roots of one fixed nonzero X polynomial. Nonsquareness,
the coefficient-ring fraction embedding and both variable-order
transports are derived, not assumed. No sampler law is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.QuadraticConstantParity
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
noncomputable section
variable {K : Type*} [Field K]

/-- Swap the two polynomial variables, then evaluate the new outer
variable at t. This equals evaluation of the original inner variable. -/
theorem swap_eval (H : Polynomial K[X]) (t : K) :
    (Polynomial.Bivariate.swap H).eval (C t) = H.map (Polynomial.evalRingHom t) := by
  induction H using Polynomial.induction_on' with
  | add P Q hp hq =>
      simp only [map_add, Polynomial.eval_add, Polynomial.map_add, hp, hq]
  | monomial n P =>
      rw [Polynomial.Bivariate.swap_monomial, Polynomial.eval_mul,
        Polynomial.eval_map_apply, Polynomial.eval_C, Polynomial.map_monomial,
        ← Polynomial.C_mul_X_pow_eq_monomial]
      rfl

/-- H has outer X and coefficient Z. The checked twist's atPoint uses
the opposite order; this is their actual symbolic equality. -/
theorem eval_eq_atPoint_swap (H : Polynomial K[X]) (t : K) :
    H.eval (C t) = QuadraticTwistObstruction.atPoint (Polynomial.Bivariate.swap H) t := by
  simpa only [Polynomial.Bivariate.swap_swap_apply, QuadraticTwistObstruction.atPoint]
    using swap_eval (Polynomial.Bivariate.swap H) t

def constantFraction : FractionRing K[X] →+* FractionRing (Polynomial K[X]) :=
  IsFractionRing.lift
    (g := (algebraMap (Polynomial K[X]) (FractionRing (Polynomial K[X]))).comp Polynomial.C)
    ((IsFractionRing.injective (Polynomial K[X]) (FractionRing (Polynomial K[X]))).comp
      Polynomial.C_injective)

theorem constantFraction_apply (d : K[X]) :
    constantFraction (algebraMap K[X] (FractionRing K[X]) d) =
      algebraMap (Polynomial K[X]) (FractionRing (Polynomial K[X])) (C d) :=
  IsFractionRing.lift_algebraMap _ d

theorem fraction_two_ne_zero [NeZero (2 : K)] :
    (2 : FractionRing (Polynomial K[X])) ≠ 0 := by
  let hom : K →+* FractionRing (Polynomial K[X]) :=
    ((algebraMap (Polynomial K[X]) (FractionRing (Polynomial K[X]))).comp
      Polynomial.C).comp Polynomial.C
  intro zero
  have equal : hom (2 : K) = hom 0 := by simpa only [map_ofNat, map_zero] using zero
  exact (NeZero.ne (2 : K)) (hom.injective equal)

def discriminant (F : Polynomial (Polynomial K[X])) : Polynomial K[X] :=
  discrim (F.coeff 2) (F.coeff 1) (F.coeff 0)

/-- The quadratic shape also holds over the polynomial coefficient ring,
not just over a field. Only three symbolic terms are expanded. -/
theorem coefficient_shape (F : Polynomial (Polynomial K[X])) (degree : F.natDegree = 2) :
    F = C (F.coeff 2)*X^2 + C (F.coeff 1)*X + C (F.coeff 0) := by
  have finite := F.as_sum_range_C_mul_X_pow' (n := 3) (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, mul_one, pow_one] at finite
  exact finite.trans (by ac_rfl)

/-- R's literal degree-zero shape and the exact fraction-field C map
derive the twist nonsquare premise from irreducibility. -/
theorem constant_remainder_nonsquare [NeZero (2 : K)]
    (F : Polynomial (Polynomial K[X])) (irreducible : Irreducible F)
    (degree : F.natDegree = 2) (H R : Polynomial K[X])
    (decomposition : discriminant F = H^2*R) (constant : R.natDegree = 0) :
    H ≠ 0 ∧ ¬ IsSquare (algebraMap K[X] (FractionRing K[X]) (R.coeff 0)) := by
  letI : NeZero (2 : FractionRing (Polynomial K[X])) := ⟨fraction_two_ne_zero⟩
  have rewritten : discrim (F.coeff 2) (F.coeff 1) (F.coeff 0) = C (R.coeff 0)*H^2 := by
    change discriminant F = _
    exact decomposition.trans
      ((congrArg (fun P => H^2*P) (Polynomial.eq_C_of_natDegree_eq_zero constant)).trans
        (mul_comm _ _))
  have inherited := QuadraticDiscriminantNonsquare.fraction_twist_nonsquare
    (L := FractionRing (Polynomial K[X])) F irreducible degree (C (R.coeff 0)) H rewritten
  refine ⟨inherited.1, ?_⟩
  intro square
  apply inherited.2
  have mapped := square.map (constantFraction (K := K))
  simpa only [constantFraction_apply] using mapped

/-- An actual OOD polynomial-root identity derives the discriminant
square identity. The supplied answer remains arbitrary. -/
theorem ood_root_discriminant_square (F : Polynomial (Polynomial K[X]))
    (degree : F.natDegree = 2) (t : K) (answer : K[X])
    (root : F.eval₂ (Polynomial.evalRingHom (C t)) answer = 0) :
    (discriminant F).eval (C t) =
      (2*(F.coeff 2).eval (C t)*answer + (F.coeff 1).eval (C t))^2 := by
  have evaluated := congrArg
    (fun P : Polynomial (Polynomial K[X]) => P.eval₂ (Polynomial.evalRingHom (C t)) answer)
    (coefficient_shape F degree)
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_evalRingHom, pow_two] at evaluated
  have quadratic : (F.coeff 2).eval (C t)*(answer*answer) +
      (F.coeff 1).eval (C t)*answer + (F.coeff 0).eval (C t) = 0 :=
    evaluated.symm.trans root
  have square := discrim_eq_sq_of_quadratic_eq_zero quadratic
  simpa only [discriminant, discrim, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_ofNat] using square

/-- F,H,R are fixed before either OOD point. Both arbitrary polynomial
answer identities force roots of the constructed leading-Z coefficient
of H (expressed through swap). Its X degree is at most degX H. -/
theorem fixed_obstruction [NeZero (2 : K)]
    (F : Polynomial (Polynomial K[X])) (irreducible : Irreducible F)
    (degree : F.natDegree = 2) (H R : Polynomial K[X])
    (decomposition : discriminant F = H^2*R) (constant : R.natDegree = 0) :
    ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ H.natDegree ∧
      E = (Polynomial.Bivariate.swap H).leadingCoeff ∧
      ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X]),
        (∀ r, F.eval₂ (Polynomial.evalRingHom (C (points r))) (answers r) = 0) →
        ∀ r, E.eval (points r) = 0 := by
  have inherited := constant_remainder_nonsquare F irreducible degree H R decomposition constant
  have swappedNonzero : Polynomial.Bivariate.swap H ≠ 0 := by
    intro zero
    apply inherited.1
    exact Polynomial.Bivariate.swap.injective
      (zero.trans (map_zero Polynomial.Bivariate.swap).symm)
  have coefficientBounds : ∀ j, ((Polynomial.Bivariate.swap H).coeff j).natDegree ≤ H.natDegree := by
    intro j
    simpa only [Polynomial.Bivariate.swap_swap_apply] using
      coeff_natDegree_le_bivariate_swap_natDegree (Polynomial.Bivariate.swap H) j
  obtain ⟨E, en, bound, chosen, forces⟩ := QuadraticTwistObstruction.exists_fixed_obstruction
    (R.coeff 0) (Polynomial.Bivariate.swap H) swappedNonzero inherited.2
    H.natDegree coefficientBounds
  refine ⟨E, en, bound, chosen, ?_⟩
  intro points answers roots
  apply forces points (fun r =>
    2*(F.coeff 2).eval (C (points r))*answers r + (F.coeff 1).eval (C (points r)))
  intro r
  have square := ood_root_discriminant_square F degree (points r) (answers r) (roots r)
  rw [decomposition, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eq_C_of_natDegree_eq_zero constant, Polynomial.eval_C,
    eval_eq_atPoint_swap] at square
  exact square.symm.trans (mul_comm _ _)

/-- Return to the source's inner-X/middle-Z/outer-Y order by literally
mapping each coefficient through Bivariate.swap. -/
def reordered (F : TrivariatePolynomial K) : Polynomial (Polynomial K[X]) :=
  F.map Polynomial.Bivariate.swap.toRingHom

theorem reordered_root (F : TrivariatePolynomial K) (t : K) (answer : K[X]) :
    (reordered F).eval₂ (Polynomial.evalRingHom (C t)) answer =
      FactorCoherence.pointSubstitution t answer F := by
  rw [Polynomial.eval₂_eq_eval_map]
  change ((F.map Polynomial.Bivariate.swap.toRingHom).map
      (Polynomial.evalRingHom (C t))).eval answer =
    (F.map (Polynomial.mapRingHom (Polynomial.evalRingHom t))).eval answer
  apply congrArg (fun P : Polynomial K[X] => P.eval answer)
  apply Polynomial.ext
  intro j
  simp only [Polynomial.coeff_map, Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom]
  exact swap_eval (F.coeff j) t

/-- Both literal source OOD identities of a fixed irreducible quadratic
in this constant-parity class imply roots of the same fixed E. -/
theorem source_fixed_obstruction [NeZero (2 : K)]
    (F : TrivariatePolynomial K) (irreducible : Irreducible F)
    (degree : F.natDegree = 2) (H R : Polynomial K[X])
    (decomposition : discriminant (reordered F) = H^2*R) (constant : R.natDegree = 0) :
    ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ H.natDegree ∧
      E = (Polynomial.Bivariate.swap H).leadingCoeff ∧
      ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X]),
        (∀ r, FactorCoherence.pointSubstitution (points r) (answers r) F = 0) →
        ∀ r, E.eval (points r) = 0 := by
  have mappedIrreducible : Irreducible (reordered F) :=
    irreducible.map (Polynomial.mapEquiv Polynomial.Bivariate.swap.toRingEquiv)
  have mappedDegree : (reordered F).natDegree = 2 :=
    (Polynomial.natDegree_map_eq_of_injective Polynomial.Bivariate.swap.injective F).trans degree
  obtain ⟨E, en, bound, chosen, forces⟩ :=
    fixed_obstruction (reordered F) mappedIrreducible mappedDegree H R decomposition constant
  refine ⟨E, en, bound, chosen, ?_⟩
  intro points answers roots
  apply forces points answers
  intro r
  exact (reordered_root F (points r) (answers r)).trans (roots r)

#print axioms swap_eval
#print axioms eval_eq_atPoint_swap
#print axioms constantFraction_apply
#print axioms fraction_two_ne_zero
#print axioms coefficient_shape
#print axioms constant_remainder_nonsquare
#print axioms ood_root_discriminant_square
#print axioms fixed_obstruction
#print axioms reordered_root
#print axioms source_fixed_obstruction
end
end AspisV8.QuadraticConstantParity
