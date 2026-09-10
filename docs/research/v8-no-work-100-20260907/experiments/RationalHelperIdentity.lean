import Mathlib.Algebra.Polynomial.Roots

/-! A symbolic regression for overstrong identity-branch recovery.
With fixed C1=0, normalized helper lanes (-b/(x-a),1/(x-a),0) produce
Z^26*(Z-b)/(x-a). Both OOD slices have degree-27 polynomial answers and
the horizontal polynomial U=0 is compatible at Z=b. Nevertheless there is
no global polynomial-in-X component curve. This leaf proves those identities
and the pole obstruction, not actual committed-source authentication, Hasse
kernel membership, relation acceptance, or a payment forgery. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000

namespace AspisV8.RationalHelperIdentity
open Polynomial
noncomputable section
variable {K : Type*} [Field K]

def numerator (b : K) : K[X] := X^26 * (X-C b)

def answer (a b t : K) : K[X] := C ((t-a)⁻¹) * numerator b

theorem numerator_ne_zero (b : K) : numerator b ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Polynomial.X_sub_C_ne_zero b)

theorem numerator_degree (b : K) : (numerator b).natDegree = 27 := by
  rw [numerator, Polynomial.natDegree_mul
    (pow_ne_zero _ Polynomial.X_ne_zero) (Polynomial.X_sub_C_ne_zero b)]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X,
    Polynomial.natDegree_X_sub_C]

/-- The retained raw degree is 27, with the selected gamma^26 factor and a
linear (hence quadratic-bounded) three-helper curve. -/
theorem numerator_eval (b gamma : K) :
    (numerator b).eval gamma = gamma^26 * (-b+gamma+0*gamma^2) := by
  simp only [numerator, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_C, zero_mul, add_zero]
  rw [sub_eq_add_neg, add_comm gamma (-b)]

theorem answer_identity (a b t : K) (noPole : t ≠ a) :
    C (t-a) * answer a b t = numerator b := by
  rw [answer, ← mul_assoc, ← Polynomial.C_mul,
    mul_inv_cancel₀ (sub_ne_zero.mpr noPole), Polynomial.C_1, one_mul]

/-- Any two nonpole OOD points have polynomial identities and both answers
agree with the horizontal original-code zero polynomial at gamma=b. In a
nonzero-challenge experiment choose b nonzero; the algebra needs no extra law. -/
theorem two_ood_compatible (a b : K) (points : Fin 2 → K)
    (noPole : ∀ r, points r ≠ a) :
    (numerator b).eval b = 0 ∧
      ∀ r, C (points r-a) * answer a b (points r) = numerator b ∧
        (answer a b (points r)).natDegree ≤ 27 ∧
        (answer a b (points r)).eval b = 0 := by
  have chosen : (numerator b).eval b = 0 := by
    simp only [numerator, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C, sub_self, mul_zero]
  refine ⟨chosen, ?_⟩
  intro r
  refine ⟨answer_identity a b (points r) (noPole r), ?_, ?_⟩
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (numerator_degree b).le
  · simp only [answer, Polynomial.eval_mul, Polynomial.eval_C, chosen, mul_zero]

/-- X is the outer variable, Z the inner polynomial variable. Evaluating
X=a rules out every polynomial component curve, of any degree. -/
theorem no_polynomial_component_curve (a b : K) :
    ¬ ∃ B : Polynomial (Polynomial K),
      (X-C (C a))*B = C (numerator b) := by
  rintro ⟨B, equation⟩
  have atPole := congrArg (fun P : Polynomial (Polynomial K) => P.eval (C a)) equation
  apply numerator_ne_zero b
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, zero_mul] using atPole.symm

/-- Cubing the cleared equation, as in the multiplicity-three interpolation
control, does not manufacture a polynomial root. -/
theorem no_cubed_polynomial_component_curve (a b : K) :
    ¬ ∃ B : Polynomial (Polynomial K),
      ((X-C (C a))*B - C (numerator b))^3 = 0 := by
  rintro ⟨B, equation⟩
  apply no_polynomial_component_curve a b
  exact ⟨B, sub_eq_zero.mp (eq_zero_of_pow_eq_zero equation)⟩

#print axioms numerator_ne_zero
#print axioms numerator_degree
#print axioms numerator_eval
#print axioms answer_identity
#print axioms two_ood_compatible
#print axioms no_polynomial_component_curve
#print axioms no_cubed_polynomial_component_curve
end
end AspisV8.RationalHelperIdentity
