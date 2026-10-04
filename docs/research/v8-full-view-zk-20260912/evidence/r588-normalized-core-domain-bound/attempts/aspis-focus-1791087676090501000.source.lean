import AspisV8R19.R585SelectedCoreNonzero
import AspisV8R17.MinorDegree

set_option autoImplicit false
namespace AspisV8R19.R588NormalizedCoreDomainBound

open MvPolynomial AspisV8R15.ExactTowerBase
open AspisV8R19.R581NormalizedCorePolynomial

noncomputable section

local instance cm31Fintype : Fintype CM31Exact :=
  Fintype.ofEquiv (M31Exact × M31Exact)
    (QuadraticAlgebra.equivProd (-1 : M31Exact) 0).symm

local instance qm31Fintype : Fintype QM31Exact :=
  Fintype.ofEquiv (CM31Exact × CM31Exact)
    (QuadraticAlgebra.equivProd qm31R 0).symm

def normalizedDet (half : QM31Exact) : MvPolynomial (Fin 3) QM31Exact :=
  (normalizedPolynomialMatrix (F := QM31Exact) half).det

theorem normalizedDet_domain_fraction_bound (half : QM31Exact)
    (S : Fin 3 → Finset QM31Exact) (m : Nat) (mpos : 0 < m)
    (domainSize : ∀ i, m ≤ (S i).card) :
    ((Finset.filter (fun s => eval s (normalizedDet half) = 0)
        (Fintype.piFinset S)).card : ℚ≥0) /
        (∏ i, ((S i).card : ℚ≥0)) ≤ (1355 : ℚ≥0) / m := by
  have hp : normalizedDet half ≠ 0 := by
    exact AspisV8R19.R585SelectedCoreNonzero.normalizedDet_ne_zero half
  have hdegree : (normalizedDet half).totalDegree ≤ 1355 := by
    exact AspisV8R19.R585SelectedCoreNonzero.normalizedDet_degree half
  apply (schwartz_zippel_sup_sum hp S).trans
  apply Finset.sup_le
  intro exponent inSupport
  calc
    (∑ i, (exponent i / (S i).card : ℚ≥0)) ≤
        ∑ i, (exponent i / m : ℚ≥0) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact_mod_cast domainSize i
    _ = ((∑ i, exponent i : Nat) : ℚ≥0) / m := by
      rw [← Finset.sum_div]
      norm_cast
    _ ≤ (1355 : ℚ≥0) / m := by
      gcongr
      have hexponent : ∑ i, exponent i ≤ 1355 := by
        have h := (le_totalDegree inSupport).trans hdegree
        rw [Finsupp.sum_fintype exponent (fun _ value => value) (fun _ => rfl)] at h
        exact h
      exact Nat.cast_le.mpr hexponent

#print axioms normalizedDet
#print axioms normalizedDet_domain_fraction_bound

end
end AspisV8R19.R588NormalizedCoreDomainBound
