import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Literal polynomial square-part/parity-part factorization, first in a
generic normalized UFD. No fraction-field denominators are introduced.
The normalization unit is absorbed in R, so D=H^2*R exactly rather than
only up to association. This leaf does not assert localization preserves
squarefreeness or a specialization preserves degree. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.PolynomialParityFactorization
open UniqueFactorizationMonoid
noncomputable section

section Product
variable {M : Type*} [CommMonoid M]

theorem power_parity (p : M) (n : Nat) :
    p^n = (p^(n/2))^2 * (if n%2=1 then p else 1) := by
  have division : n = n/2*2 + n%2 := by omega
  have remainder : n%2 < 2 := Nat.mod_lt _ (by decide)
  calc
    p^n = p^(n/2*2+n%2) := congrArg (fun k => p^k) division
    _ = (p^(n/2))^2 * p^(n%2) := by rw [pow_add, pow_mul]
    _ = (p^(n/2))^2 * (if n%2=1 then p else 1) := by
      congr 1
      split_ifs with odd
      · rw [odd, pow_one]
      · have even : n%2=0 := by omega
        rw [even, pow_zero]

def halfProduct (s : Multiset M) : M := by
  classical
  exact ∏ p ∈ s.toFinset, p^(s.count p/2)

def oddSupport (s : Multiset M) : Finset M := by
  classical
  exact s.toFinset.filter (fun p => s.count p%2=1)

def oddProduct (s : Multiset M) : M := ∏ p ∈ oddSupport s, p

theorem multiset_product_parity (s : Multiset M) :
    s.prod = (halfProduct s)^2 * oddProduct s := by
  classical
  rw [Finset.prod_multiset_count]
  calc
    (∏ p ∈ s.toFinset, p^s.count p) =
        ∏ p ∈ s.toFinset, (p^(s.count p/2))^2 *
          (if s.count p%2=1 then p else 1) := by
      apply Finset.prod_congr rfl
      intro p _
      exact power_parity p (s.count p)
    _ = (halfProduct s)^2 * oddProduct s := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow]
      simp only [halfProduct, oddProduct, oddSupport, Finset.prod_filter]
end Product

section Factorization
variable {M : Type*} [CommMonoidWithZero M] [Nontrivial M]
  [NormalizationMonoid M] [UniqueFactorizationMonoid M]

theorem odd_factors_squarefree (D : M) :
    Squarefree (oddProduct (normalizedFactors D)) := by
  classical
  unfold oddProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq different
    have pMember : p ∈ normalizedFactors D :=
      Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have qMember : q ∈ normalizedFactors D :=
      Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    apply (irreducible_of_normalized_factor p pMember).isRelPrime_iff_not_dvd.mpr
    intro divides
    exact different (normalizedFactors_eq_of_dvd D p pMember q qMember divides)
  · intro p hp
    have member : p ∈ normalizedFactors D :=
      Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    exact (irreducible_of_normalized_factor p member).squarefree

/-- All powers and the remaining unit live in the original UFD. For
M=K[Z][X], the witnesses are literal bivariate polynomials. Odd Z-content
is retained inside R, with no need to separate an extra scalar factor. -/
theorem exists_squarefree_remainder (D : M) (nonzero : D ≠ 0) :
    ∃ H R : M, H ≠ 0 ∧ R ≠ 0 ∧ D = H^2*R ∧ Squarefree R := by
  classical
  obtain ⟨unit, factorization⟩ := prod_normalizedFactors nonzero
  let H := halfProduct (normalizedFactors D)
  let R := oddProduct (normalizedFactors D) * (unit : M)
  have identity : D = H^2*R := by
    rw [← factorization, multiset_product_parity]
    exact mul_assoc _ _ _
  have associated : Associated (oddProduct (normalizedFactors D)) R :=
    ⟨unit, rfl⟩
  have squarefree : Squarefree R :=
    associated.squarefree_iff.mp (odd_factors_squarefree D)
  refine ⟨H, R, ?_, squarefree.ne_zero, identity, squarefree⟩
  intro zero
  apply nonzero
  rw [identity, zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
end Factorization

#print axioms power_parity
#print axioms multiset_product_parity
#print axioms odd_factors_squarefree
#print axioms exists_squarefree_remainder
end
end AspisV8.PolynomialParityFactorization
