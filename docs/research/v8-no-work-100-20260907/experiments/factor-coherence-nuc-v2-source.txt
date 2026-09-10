import AspisFormal.K1.V7ExactCorrelatedAgreementSmooth

/-! A polynomial OOD answer selects a global factor before gamma.
Every later horizontal polynomial candidate satisfying the same OOD value
belongs to that factor unless the actual parent derivative vanishes there.
The derivative can vanish identically: no squarefreeness is assumed, and
that branch is explicitly retained. This is factor coherence, not a
component-tuple, extractor-access, or payment theorem. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.FactorCoherence
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
noncomputable section
variable {K : Type*} [Field K]

/-- Substitute the actual OOD point into X and the whole answer polynomial
into Y, leaving the challenge variable Z symbolic. -/
def pointSubstitution (x : K) (answer : K[X]) :
    TrivariatePolynomial K →+* K[X] :=
  (Polynomial.evalRingHom answer).comp (specializeEvaluationPoint x)

def derivativeCurve (P : TrivariatePolynomial K) (x : K) (answer : K[X]) : K[X] :=
  pointSubstitution x answer P.derivative

theorem pointSubstitution_eval (P : TrivariatePolynomial K)
    (x gamma : K) (answer : K[X]) :
    (pointSubstitution x answer P).eval gamma =
      (specializeEvaluationPointChallenge x gamma P).eval (answer.eval gamma) := by
  change ((specializeEvaluationPoint x P).eval answer).eval gamma =
    ((specializeEvaluationPoint x P).map (Polynomial.evalRingHom gamma)).eval
      (answer.eval gamma)
  rw [Polynomial.eval_map]
  exact (Polynomial.eval₂_at_apply (p := specializeEvaluationPoint x P)
    (Polynomial.evalRingHom gamma) answer).symm

/-- The exact product-rule alternative. U is an arbitrary later polynomial,
not a member of a retrospectively supplied component curve. -/
theorem candidate_factor_or_collision
    (P F H : TrivariatePolynomial K) (x gamma : K) (answer U : K[X])
    (product : P = F * H)
    (identity : pointSubstitution x answer F = 0)
    (root : challengeCandidateHom gamma U P = 0)
    (point : U.eval x = answer.eval gamma) :
    challengeCandidateHom gamma U F = 0 ∨
      (derivativeCurve P x answer).eval gamma = 0 := by
  have roots : challengeCandidateHom gamma U F *
      challengeCandidateHom gamma U H = 0 := by
    rw [← map_mul, ← product]
    exact root
  rcases mul_eq_zero.mp roots with factorRoot | otherRoot
  · exact Or.inl factorRoot
  · right
    have factorAtPoint : (specializeEvaluationPointChallenge x gamma F).eval
        (U.eval x) = 0 := by
      rw [point, ← pointSubstitution_eval, identity, Polynomial.eval_zero]
    have otherAtPoint : (specializeEvaluationPointChallenge x gamma H).eval
        (U.eval x) = 0 := by
      rw [specializeEvaluationPointChallenge_eval_candidate, otherRoot,
        Polynomial.eval_zero]
    unfold derivativeCurve
    rw [pointSubstitution_eval, ← point, product, Polynomial.derivative_mul,
      map_add, map_mul, map_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, factorAtPoint, otherAtPoint]
    simp only [mul_zero, zero_mul, add_zero]

theorem candidate_factor_of_simple
    (P F H : TrivariatePolynomial K) (x gamma : K) (answer U : K[X])
    (product : P = F * H)
    (identity : pointSubstitution x answer F = 0)
    (root : challengeCandidateHom gamma U P = 0)
    (point : U.eval x = answer.eval gamma)
    (simple : (derivativeCurve P x answer).eval gamma ≠ 0) :
    challengeCandidateHom gamma U F = 0 :=
  (candidate_factor_or_collision P F H x gamma answer U product identity root point).resolve_right
    simple

/-- A nonzero derivative curve excludes a zero whole-parent specialization
at this actual OOD point. It does not assume such regularity automatically. -/
theorem specialization_ne_zero_of_derivative
    (P : TrivariatePolynomial K) (x : K) (answer : K[X])
    (regular : derivativeCurve P x answer ≠ 0) :
    specializeEvaluationPoint x P ≠ 0 := by
  intro zero
  apply regular
  change ((specializeEvaluationPoint x P.derivative).eval answer) = 0
  have derivativeMap : specializeEvaluationPoint x P.derivative =
      (specializeEvaluationPoint x P).derivative := by
    exact (Polynomial.derivative_map P (evaluateInnerVariable x)).symm
  rw [derivativeMap, zero, Polynomial.derivative_zero, Polynomial.eval_zero]

/-- Select from the existing fixed global prime-factor multiset using the
entire OOD polynomial identity, before seeing any gamma or candidate. -/
theorem exists_positive_factor_identity
    (P : TrivariatePolynomial K) (nonzero : P ≠ 0)
    (x : K) (answer : K[X])
    (specialization : specializeEvaluationPoint x P ≠ 0)
    (identity : pointSubstitution x answer P = 0) :
    ∃ F ∈ curvePrimeFactors P,
      0 < F.natDegree ∧ pointSubstitution x answer F = 0 := by
  classical
  let factors := curvePrimeFactors P
  have associated := curvePrimeFactors_product_associated P nonzero
  have mapped := associated.map (pointSubstitution x answer)
  have productZero : (factors.map (pointSubstitution x answer)).prod = 0 := by
    rw [← map_multiset_prod]
    exact mapped.eq_zero_iff.mpr identity
  have zeroMem : (0 : K[X]) ∈ factors.map (pointSubstitution x answer) :=
    Multiset.prod_eq_zero_iff.mp productZero
  rw [Multiset.mem_map] at zeroMem
  obtain ⟨F, member, factorIdentity⟩ := zeroMem
  refine ⟨F, member, ?_, factorIdentity⟩
  have divides : F ∣ P :=
    (Multiset.dvd_prod member).trans associated.dvd
  by_contra notPositive
  have constant : F = C (F.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (by omega)
  have specializedZero : specializeEvaluationPoint x F = 0 := by
    rw [constant] at factorIdentity ⊢
    simpa only [pointSubstitution, RingHom.coe_comp, Function.comp_apply,
      specializeEvaluationPoint, Polynomial.coe_mapRingHom, Polynomial.map_C,
      Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.C_0] using
      congrArg C factorIdentity
  have specializedDivides := _root_.map_dvd (specializeEvaluationPoint x) divides
  rw [specializedZero, zero_dvd_iff] at specializedDivides
  exact specialization specializedDivides

/-- A fixed pre-gamma factor works uniformly for all adaptive candidates.
The identity-derivative branch is explicit, and no bound is assigned to it. -/
theorem fixed_factor_or_singular
    (P : TrivariatePolynomial K) (nonzero : P ≠ 0)
    (x : K) (answer : K[X])
    (identity : pointSubstitution x answer P = 0) :
    derivativeCurve P x answer = 0 ∨
      ∃ F ∈ curvePrimeFactors P,
        0 < F.natDegree ∧ pointSubstitution x answer F = 0 ∧
        ∀ gamma (U : K[X]),
          challengeCandidateHom gamma U P = 0 →
          U.eval x = answer.eval gamma →
          (derivativeCurve P x answer).eval gamma ≠ 0 →
          challengeCandidateHom gamma U F = 0 := by
  classical
  by_cases singular : derivativeCurve P x answer = 0
  · exact Or.inl singular
  · right
    obtain ⟨F, member, positive, factorIdentity⟩ :=
      exists_positive_factor_identity P nonzero x answer
        (specialization_ne_zero_of_derivative P x answer singular) identity
    refine ⟨F, member, positive, factorIdentity, ?_⟩
    have divides : F ∣ P :=
      (Multiset.dvd_prod member).trans
        (curvePrimeFactors_product_associated P nonzero).dvd
    obtain ⟨H, product⟩ := divides
    intro gamma U root point simple
    exact candidate_factor_of_simple P F H x gamma answer U product factorIdentity
      root point simple

/-- The actual identity supplies a monic degree-one local divisor. This
does not claim it is already the canonical normalized factor representative. -/
theorem identity_linear_local_divisor
    (P : TrivariatePolynomial K) (x : K) (answer : K[X])
    (identity : pointSubstitution x answer P = 0) :
    (X - C answer : BivariatePolynomial K) ∣ specializeEvaluationPoint x P ∧
      (X - C answer : BivariatePolynomial K).Monic ∧
      (X - C answer : BivariatePolynomial K).natDegree = 1 := by
  refine ⟨Polynomial.dvd_iff_isRoot.mpr identity, Polynomial.monic_X_sub_C _,
    Polynomial.natDegree_X_sub_C _⟩

#print axioms pointSubstitution_eval
#print axioms candidate_factor_or_collision
#print axioms candidate_factor_of_simple
#print axioms specialization_ne_zero_of_derivative
#print axioms exists_positive_factor_identity
#print axioms fixed_factor_or_singular
#print axioms identity_linear_local_divisor
end
end AspisV8.FactorCoherence
