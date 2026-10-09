import FactorIdentityCover

/-! A pre-OOD obstruction polynomial for monic linear factors.  If the
unique polynomial root has gamma degree above the answer-row degree, an
actual polynomial OOD identity forces one fixed nonzero X coefficient to
vanish.  Multiplying over the fixed parent factors charges the additive
parent X degree, not the number of adaptively selected candidates.
This does not assume that every retained factor is monic or linear. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.MonicFactorOOD
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisV8.FactorCoherence AspisV8.FactorIdentityCover
noncomputable section
variable {K : Type*} [Field K]
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- Outer Z, inner X; this is derived from the factor, not a supplied tuple. -/
def rootCurve (F : TrivariatePolynomial K) : Polynomial K[X] := -F.coeff 0

theorem monic_linear_form (F : TrivariatePolynomial K)
    (monic : F.Monic) (linear : F.natDegree = 1) :
    F = X - C (rootCurve F) := by
  calc
    F = X + C (F.coeff 0) := monic.eq_X_add_C linear
    _ = X - C (rootCurve F) := by
      rw [rootCurve, Polynomial.C_neg]
      ring

theorem candidate_eq_curve (F : TrivariatePolynomial K)
    (monic : F.Monic) (linear : F.natDegree = 1)
    (gamma : K) (U : K[X]) (root : challengeCandidateHom gamma U F = 0) :
    U = (rootCurve F).eval (C gamma) := by
  rw [monic_linear_form F monic linear] at root
  simpa only [challengeCandidateHom, RingHom.coe_comp, Function.comp_apply,
    specializeChallenge, Polynomial.coe_mapRingHom, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, substituteCandidate,
    Polynomial.coe_evalRingHom, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] using root

theorem identity_eq_curve (F : TrivariatePolynomial K)
    (monic : F.Monic) (linear : F.natDegree = 1)
    (x : K) (answer : K[X]) (identity : pointSubstitution x answer F = 0) :
    answer = (rootCurve F).map (Polynomial.evalRingHom x) := by
  rw [monic_linear_form F monic linear] at identity
  simpa only [pointSubstitution, RingHom.coe_comp, Function.comp_apply,
    specializeEvaluationPoint, Polynomial.coe_mapRingHom, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Polynomial.coe_evalRingHom,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    evaluateInnerVariable, sub_eq_zero] using identity

theorem root_coefficient_x_degree (F : TrivariatePolynomial K) (j : Nat) :
    ((rootCurve F).coeff j).natDegree ≤ (trivariateXOuterEquiv K F).natDegree := by
  have bound := reorderFactorCoefficients_coeff_natDegree_le F 0
  have inner := coeff_natDegree_le_bivariate_swap_natDegree (F.coeff 0) j
  have bound' : (Polynomial.Bivariate.swap (F.coeff 0)).natDegree ≤
      (trivariateXOuterEquiv K F).natDegree := by
    rw [reorderFactorCoefficients, Polynomial.coeff_map] at bound
    exact bound
  simpa only [rootCurve, Polynomial.coeff_neg, Polynomial.natDegree_neg] using
    inner.trans bound'

/-- One coefficient is chosen from F alone, before either OOD point or
answer.  No field enumeration or point-dependent root selection. -/
theorem exists_excess_coefficient (degree : Nat) (F : TrivariatePolynomial K)
    (excess : degree < (rootCurve F).natDegree) :
    ∃ H : K[X], H ≠ 0 ∧ H.natDegree ≤ (trivariateXOuterEquiv K F).natDegree ∧
      ∀ x (answer : K[X]), F.Monic → F.natDegree = 1 →
        answer.natDegree ≤ degree → pointSubstitution x answer F = 0 → H.eval x = 0 := by
  let j := (rootCurve F).natDegree
  have nonzero : rootCurve F ≠ 0 := by
    intro zero
    simp only [zero, Polynomial.natDegree_zero] at excess
    omega
  refine ⟨(rootCurve F).coeff j, Polynomial.leadingCoeff_ne_zero.mpr nonzero,
    root_coefficient_x_degree F j, ?_⟩
  intro x answer monic linear answerDegree identity
  have equality := congrArg (fun p : K[X] => p.coeff j)
    (identity_eq_curve F monic linear x answer identity)
  rw [Polynomial.coeff_map] at equality
  exact equality.symm.trans (Polynomial.coeff_eq_zero_of_natDegree_lt
    (answerDegree.trans_lt excess))

/-- All factors, including repeats/content, share the parent's X degree. -/
theorem all_factor_x_degrees_le (P : TrivariatePolynomial K) (nonzero : P ≠ 0) :
    ((curvePrimeFactors P).map (fun F => (trivariateXOuterEquiv K F).natDegree)).sum ≤
      (trivariateXOuterEquiv K P).natDegree := by
  classical
  let factors := (curvePrimeFactors P).map (trivariateXOuterEquiv K)
  have associated := (curvePrimeFactors_product_associated P nonzero).map
    (trivariateXOuterEquiv K).toRingHom
  have prodDvd : factors.prod ∣ trivariateXOuterEquiv K P := by
    change ((curvePrimeFactors P).map (trivariateXOuterEquiv K).toRingHom).prod ∣
      (trivariateXOuterEquiv K).toRingHom P
    rw [← map_multiset_prod]
    exact associated.dvd
  have parentNonzero : trivariateXOuterEquiv K P ≠ 0 := by
    simpa only [map_zero] using (trivariateXOuterEquiv K).injective.ne nonzero
  have zeroNotMem : (0 : TrivariatePolynomial K) ∉ factors := by
    intro member
    obtain ⟨F, member, zero⟩ := Multiset.mem_map.mp member
    have fzero : F = 0 := (trivariateXOuterEquiv K).injective
      (zero.trans (map_zero (trivariateXOuterEquiv K)).symm)
    exact (curvePrimeFactors_prime P nonzero F member).ne_zero fzero
  have degree := Polynomial.natDegree_le_of_dvd prodDvd parentNonzero
  rw [Polynomial.natDegree_multiset_prod factors zeroNotMem] at degree
  simpa only [factors, Multiset.map_map, Function.comp_def] using degree

private theorem product_degree_le {I : Type*} (factors : Multiset I)
    (beta : I → K[X]) (weight : I → Nat)
    (bounds : ∀ F ∈ factors, (beta F).natDegree ≤ weight F) :
    (factors.map beta).prod.natDegree ≤ (factors.map weight).sum := by
  induction factors using Multiset.induction_on with
  | empty => simp
  | @cons F rest induction =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact Polynomial.natDegree_mul_le.trans <| Nat.add_le_add
      (bounds F (Multiset.mem_cons_self F rest))
      (induction fun H member => bounds H (Multiset.mem_cons_of_mem member))

/-- Constructed before the OOD points. Answers can depend on those points
in any sequential way; a retained excessive-degree monic factor forces BOTH
points to be roots of this one polynomial. This is not an actual FS sampler
theorem and does not cover the non-monic/higher-Y remainder. -/
theorem exists_parent_ood_obstruction (degree : Nat)
    (P : TrivariatePolynomial K) (nonzero : P ≠ 0) :
    ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ (trivariateXOuterEquiv K P).natDegree ∧
      ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X])
        (F : TrivariatePolynomial K), F ∈ curvePrimeFactors P →
        F.Monic → F.natDegree = 1 → Retained points answers F →
        (∀ r, (answers r).natDegree ≤ degree) →
        (rootCurve F).natDegree ≤ degree ∨ ∀ r, E.eval (points r) = 0 := by
  classical
  let factors := curvePrimeFactors P
  let beta : TrivariatePolynomial K → K[X] := fun F =>
    if excess : degree < (rootCurve F).natDegree then
      Classical.choose (exists_excess_coefficient degree F excess)
    else 1
  have properties : ∀ F, beta F ≠ 0 ∧
      (beta F).natDegree ≤ (trivariateXOuterEquiv K F).natDegree ∧
      ∀ x (answer : K[X]), F.Monic → F.natDegree = 1 →
        answer.natDegree ≤ degree → pointSubstitution x answer F = 0 →
        (rootCurve F).natDegree ≤ degree ∨ (beta F).eval x = 0 := by
    intro F
    by_cases excess : degree < (rootCurve F).natDegree
    · simpa only [beta, dif_pos excess] using
        (show (Classical.choose (exists_excess_coefficient degree F excess)) ≠ 0 ∧
            _ ∧ _ from ⟨(Classical.choose_spec (exists_excess_coefficient degree F excess)).1,
          (Classical.choose_spec (exists_excess_coefficient degree F excess)).2.1,
          fun x answer monic linear bound identity => Or.inr
            ((Classical.choose_spec (exists_excess_coefficient degree F excess)).2.2
              x answer monic linear bound identity)⟩)
    · simp only [beta, dif_neg excess]
      exact ⟨one_ne_zero, by simp, fun _ _ _ _ _ _ => Or.inl (Nat.le_of_not_gt excess)⟩
  let E := (factors.map beta).prod
  have Ezero : E ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro member
    obtain ⟨F, _, zero⟩ := Multiset.mem_map.mp member
    exact (properties F).1 zero
  refine ⟨E, Ezero,
    (product_degree_le factors beta (fun F => (trivariateXOuterEquiv K F).natDegree)
      (fun F _ => (properties F).2.1)).trans (all_factor_x_degrees_le P nonzero), ?_⟩
  intro points answers F member monic linear retained bounds
  by_cases small : (rootCurve F).natDegree ≤ degree
  · exact Or.inl small
  · right
    intro r
    have root := ((properties F).2.2 (points r) (answers r) monic linear
      (bounds r) (retained.2 r)).resolve_left small
    obtain ⟨rest, product⟩ := (Multiset.dvd_prod
      (Multiset.mem_map.mpr ⟨F, member, rfl⟩) : beta F ∣ E)
    change ((factors.map beta).prod).eval (points r) = 0
    rw [product, Polynomial.eval_mul, root, zero_mul]

/-- Exact ideal pair count. The checked pre-OOD obstruction supplies E;
uniform independent sampling is a separate experiment-level interpretation. -/
theorem pair_root_card_le (E : K[X]) (nonzero : E ≠ 0) (S T : Finset K) :
    ((S ×ˢ T).filter (fun pair : K × K => E.eval pair.1 = 0 ∧ E.eval pair.2 = 0)).card ≤
      E.natDegree * E.natDegree := by
  classical
  have one : ∀ A : Finset K, (A.filter (fun x => E.eval x = 0)).card ≤ E.natDegree := by
    intro A
    apply Polynomial.card_le_degree_of_subset_roots
    intro x member
    exact (Polynomial.mem_roots nonzero).mpr (Finset.mem_filter.mp member).2
  have product : (S ×ˢ T).filter (fun pair : K × K => E.eval pair.1 = 0 ∧ E.eval pair.2 = 0) =
      (S.filter fun x => E.eval x = 0) ×ˢ (T.filter fun x => E.eval x = 0) := by
    ext pair
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [product, Finset.card_product]
  exact Nat.mul_le_mul (one S) (one T)

#print axioms monic_linear_form
#print axioms candidate_eq_curve
#print axioms identity_eq_curve
#print axioms root_coefficient_x_degree
#print axioms exists_excess_coefficient
#print axioms all_factor_x_degrees_le
#print axioms exists_parent_ood_obstruction
#print axioms pair_root_card_le
end
end AspisV8.MonicFactorOOD
