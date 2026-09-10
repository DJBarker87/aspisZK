import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Polynomial.Roots

/-! Fixed linear constraints do not make an adaptive solution a polynomial
curve. Either a separating functional bounds the number of feasible scalars,
or there is a fixed particular curve and an unrestricted kernel offset.

This is an abstract vector-space reduction. No selected MLE/chord map,
retained factor, support predicate, transcript distribution or extraction
success is assumed to have been instantiated here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.FixedLinearMapCurveReduction
open Polynomial Finset
noncomputable section
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] {d : Nat}

def curve (b : Fin (d + 1) → V) (gamma : K) : V :=
  ∑ i, gamma ^ i.val • b i

def scalarPolynomial (phi : W →ₗ[K] K) (b : Fin (d + 1) → W) : K[X] :=
  ∑ i, Polynomial.monomial i.val (phi (b i))

def feasible (L : V →ₗ[K] W) (b : Fin (d + 1) → W)
    (Gamma : Finset K) : Finset K := by
  classical
  exact Gamma.filter fun gamma => curve b gamma ∈ LinearMap.range L

theorem scalar_coeff (phi : W →ₗ[K] K) (b : Fin (d + 1) → W)
    (i : Fin (d + 1)) :
    (scalarPolynomial phi b).coeff i.val = phi (b i) := by
  classical
  simp [scalarPolynomial, Polynomial.coeff_monomial, Fin.val_inj]

theorem scalar_degree (phi : W →ₗ[K] K) (b : Fin (d + 1) → W) :
    (scalarPolynomial phi b).natDegree ≤ d := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp i.isLt)

theorem scalar_eval (phi : W →ₗ[K] K) (b : Fin (d + 1) → W) (gamma : K) :
    (scalarPolynomial phi b).eval gamma = phi (curve b gamma) := by
  classical
  simp only [scalarPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    curve, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem curve_map (L : V →ₗ[K] W) (p : Fin (d + 1) → V)
    (b : Fin (d + 1) → W) (lifts : ∀ i, L (p i) = b i) (gamma : K) :
    L (curve p gamma) = curve b gamma := by
  classical
  simp only [curve, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [lifts i]

/-- One nonzero separating scalar polynomial suffices. The small set is
the set of feasible scalars, not the set of infeasible scalars. -/
theorem feasible_card_of_separator (L : V →ₗ[K] W)
    (b : Fin (d + 1) → W) (Gamma : Finset K) (phi : W →ₗ[K] K)
    (annihilates : ∀ v, phi (L v) = 0)
    (i : Fin (d + 1)) (nonzero : phi (b i) ≠ 0) :
    (feasible L b Gamma).card ≤ d := by
  classical
  have polynomialNonzero : scalarPolynomial phi b ≠ 0 := by
    intro zero
    have coefficient := scalar_coeff phi b i
    rw [zero, Polynomial.coeff_zero] at coefficient
    exact nonzero coefficient.symm
  have roots : (feasible L b Gamma).val ⊆ (scalarPolynomial phi b).roots := by
    intro gamma member
    have rangeMember := (Finset.mem_filter.mp member).2
    obtain ⟨v, equal⟩ := rangeMember
    apply (Polynomial.mem_roots polynomialNonzero).mpr
    change (scalarPolynomial phi b).eval gamma = 0
    rw [scalar_eval, ← equal]
    exact annihilates v
  exact (Polynomial.card_le_degree_of_subset_roots roots).trans (scalar_degree phi b)

/-- The separator is derived from a coefficient outside the fixed range;
it is not supplied as a cryptographic or source hypothesis. -/
theorem feasible_card_of_coefficient_outside (L : V →ₗ[K] W)
    (b : Fin (d + 1) → W) (Gamma : Finset K)
    (i : Fin (d + 1)) (outside : b i ∉ LinearMap.range L) :
    (feasible L b Gamma).card ≤ d := by
  classical
  obtain ⟨phi, nonzero, imageZero⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem outside inferInstance
  have annihilates : ∀ v, phi (L v) = 0 := by
    intro v
    have member : phi (L v) ∈ (LinearMap.range L).map phi :=
      Submodule.mem_map.mpr ⟨L v, ⟨v, rfl⟩, rfl⟩
    rw [imageZero] at member
    simpa using member
  exact feasible_card_of_separator L b Gamma phi annihilates i nonzero

theorem solution_iff_kernel_offset (L : V →ₗ[K] W)
    (p : Fin (d + 1) → V) (b : Fin (d + 1) → W)
    (lifts : ∀ i, L (p i) = b i) (gamma : K) (v : V) :
    L v = curve b gamma ↔ v - curve p gamma ∈ LinearMap.ker L := by
  rw [LinearMap.mem_ker, map_sub, curve_map L p b lifts, sub_eq_zero]

/-- Quantifier order: L and b are fixed, then a single tuple p is chosen,
then gamma and v are arbitrary. In particular v may come from any adaptive
post-alpha continuation. Nothing restricts its kernel offset. -/
theorem range_kernel_dichotomy (L : V →ₗ[K] W)
    (b : Fin (d + 1) → W) (Gamma : Finset K) :
    (feasible L b Gamma).card ≤ d ∨
      ∃ p : Fin (d + 1) → V, (∀ i, L (p i) = b i) ∧
        ∀ (gamma : K) (v : V),
          L v = curve b gamma ↔ v - curve p gamma ∈ LinearMap.ker L := by
  classical
  by_cases inRange : ∀ i, b i ∈ LinearMap.range L
  · have lifts : ∀ i, ∃ v, L v = b i := inRange
    obtain ⟨p, hp⟩ := Classical.axiom_of_choice lifts
    exact Or.inr ⟨p, hp, solution_iff_kernel_offset L p b hp⟩
  · obtain ⟨i, outside⟩ := not_forall.mp inRange
    exact Or.inl (feasible_card_of_coefficient_outside L b Gamma i outside)

/-- More than d feasible values yields a fixed particular curve, not a
coherent representation of every later accepted candidate by that curve. -/
theorem dense_feasible_particular_curve (L : V →ₗ[K] W)
    (b : Fin (d + 1) → W) (Gamma : Finset K)
    (dense : d < (feasible L b Gamma).card) :
    ∃ p : Fin (d + 1) → V, (∀ i, L (p i) = b i) ∧
      ∀ (gamma : K) (v : V),
        L v = curve b gamma ↔ v - curve p gamma ∈ LinearMap.ker L := by
  rcases range_kernel_dichotomy L b Gamma with sparse | particular
  · exact False.elim (Nat.not_lt_of_ge sparse dense)
  · exact particular

#print axioms scalar_coeff
#print axioms scalar_degree
#print axioms scalar_eval
#print axioms curve_map
#print axioms feasible_card_of_separator
#print axioms feasible_card_of_coefficient_outside
#print axioms solution_iff_kernel_offset
#print axioms range_kernel_dichotomy
#print axioms dense_feasible_particular_curve
end
end AspisV8.FixedLinearMapCurveReduction

