import QuadraticSpecializationTotal
import QuadraticResultantDescent
import PolynomialParityLocalization
import AspisFormal.K1.V7ExactCorrelatedAgreementSmooth

/-! A decomposition constructed from the fixed discriminant, with a total
root-event bound on its positive-X parity branch. The constant-X twist
branch remains explicit rather than being thrown away.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.QuadraticConstructedParity
noncomputable section
open Polynomial

def RootsAt {K : Type*} [Field K]
    (a b c : Polynomial K[X]) (gamma : K) : Prop :=
  ∃ U : K[X], a.map (Polynomial.evalRingHom gamma)*U^2 +
    b.map (Polynomial.evalRingHom gamma)*U + c.map (Polynomial.evalRingHom gamma) = 0

theorem positive_parity_bound
    {K : Type*} [Field K] (p : Nat) [CharP K p]
    (a b c H R : Polynomial K[X]) (hNonzero : H ≠ 0)
    (decomposition : b^2-4*a*c = H^2*R)
    (positive : 0 < R.natDegree) (small : R.natDegree < p)
    (squarefree : Squarefree (R.map (algebraMap K[X] (FractionRing K[X]))))
    (G : Finset K) (roots : ∀ gamma ∈ G, RootsAt a b c gamma) :
    G.card ≤ (Polynomial.Bivariate.swap H).natDegree +
      4*(Polynomial.Bivariate.swap R).natDegree := by
  have hc := AspisK1.V7ExactCorrelatedAgreementSmooth.coeff_natDegree_le_bivariate_swap_natDegree H
  have rc := AspisK1.V7ExactCorrelatedAgreementSmooth.coeff_natDegree_le_bivariate_swap_natDegree R
  rcases Nat.even_or_odd R.natDegree with even | odd
  · obtain ⟨m, hm⟩ := even
    have degree : R.natDegree = 2*m := by omega
    have mPositive : 0 < m := by omega
    have resultant := QuadraticResultantDescent.fixed_resultant_nonzero p R positive small squarefree
    rw [degree] at resultant
    exact QuadraticSpecializationTotal.total_even_roots_card_le a b c H R m
      (Polynomial.Bivariate.swap H).natDegree (Polynomial.Bivariate.swap R).natDegree
      mPositive hNonzero decomposition (by omega) hc rc resultant G roots
  · have bounded := QuadraticSpecializationTotal.total_odd_roots_card_le a b c H R
      (Polynomial.Bivariate.swap H).natDegree (Polynomial.Bivariate.swap R).natDegree
      hNonzero odd decomposition hc rc G roots
    omega

theorem exists_fixed_parity_dichotomy
    {K : Type*} [Field K] (p : Nat) [CharP K p]
    (a b c : Polynomial K[X])
    (nonzero : b^2-4*a*c ≠ 0) (small : (b^2-4*a*c).natDegree < p) :
    ∃ H R : Polynomial K[X], H ≠ 0 ∧ R ≠ 0 ∧ b^2-4*a*c = H^2*R ∧
      Squarefree (R.map (algebraMap K[X] (FractionRing K[X]))) ∧
      (R.natDegree = 0 ∨ ∀ G : Finset K,
        (∀ gamma ∈ G, RootsAt a b c gamma) →
        G.card ≤ 4*(Polynomial.Bivariate.swap (b^2-4*a*c)).natDegree) := by
  obtain ⟨H, R, hn, rn, identity, _, squarefree, xDegree, zDegree⟩ :=
    PolynomialParityLocalization.bivariate_parity (b^2-4*a*c) nonzero
  refine ⟨H, R, hn, rn, identity, squarefree, ?_⟩
  by_cases zero : R.natDegree = 0
  · exact Or.inl zero
  · right
    intro G roots
    have rPositive : 0 < R.natDegree := Nat.pos_of_ne_zero zero
    have rSmall : R.natDegree < p := by omega
    have bounded := positive_parity_bound p a b c H R hn identity
      rPositive rSmall squarefree G roots
    omega

#print axioms positive_parity_bound
#print axioms exists_fixed_parity_dichotomy
end
end AspisV8.QuadraticConstructedParity
