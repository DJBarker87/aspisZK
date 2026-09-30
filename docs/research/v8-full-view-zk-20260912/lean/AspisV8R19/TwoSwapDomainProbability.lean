import AspisV8R19.TwoSwapFixedRootProbability

/-! Schwartz--Zippel with coordinate-specific accepted challenge domains.

This is the form needed for full-field, nonzero and secure-circle parameter
samplers.  It does not assert that the source sampler realizes these product
domains, and it does not yet account for the second circle parameter excluding
the first one. -/
set_option autoImplicit false
namespace AspisR19.TwoSwapDomainProbability
open MvPolynomial AspisV8R15.ExactTowerBase QM31ResidualWitness
open TwoSwapFixedRootProbability
noncomputable section

local instance : NeZero (2:QM31Exact) := ⟨by
  intro h
  have hz : (2:RootCertificate.M)=0 := embed_injective (by simpa only [map_ofNat,map_zero] using h)
  exact (by decide : (2:RootCertificate.M)≠0) hz⟩

local instance cm31Fintype : Fintype CM31Exact :=
  Fintype.ofEquiv (M31Exact × M31Exact)
    (QuadraticAlgebra.equivProd (-1 : M31Exact) 0).symm

local instance qm31Fintype : Fintype QM31Exact :=
  Fintype.ofEquiv (CM31Exact × CM31Exact)
    (QuadraticAlgebra.equivProd qm31R 0).symm

theorem schwartz_zippel_min_card {p : MvPolynomial (Fin 36) QM31Exact}
    (hp : p ≠ 0) (degree : p.totalDegree ≤ 819)
    (S : Fin 36 → Finset QM31Exact) (m : Nat) (mpos : 0 < m)
    (domainSize : ∀ i, m ≤ (S i).card) :
    ((Finset.filter (fun s => eval s p = 0) (Fintype.piFinset S)).card : ℚ≥0) /
        (∏ i, ((S i).card : ℚ≥0)) ≤ (819 : ℚ≥0) / m := by
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
    _ ≤ (819 : ℚ≥0) / m := by
      gcongr
      have hexponent : ∑ i, exponent i ≤ 819 := by
        have h := (le_totalDegree inSupport).trans degree
        rw [Finsupp.sum_fintype exponent (fun _ value => value) (fun _ => rfl)] at h
        exact h
      exact Nat.cast_le.mpr hexponent

theorem fixed_root_domains (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) (S : Fin 36 → Finset QM31Exact) (m : Nat)
    (mpos : 0 < m) (domainSize : ∀ i, m ≤ (S i).card) :
    ((Finset.filter (fun s => eval s (determinantFor t ht noneOne) = 0)
        (Fintype.piFinset S)).card : ℚ≥0) /
        (∏ i, ((S i).card : ℚ≥0)) ≤ (819 : ℚ≥0) / m :=
  schwartz_zippel_min_card (determinant_ne_zero t ht noneOne)
    (determinant_degree t ht noneOne) S m mpos domainSize

#print axioms schwartz_zippel_min_card
#print axioms fixed_root_domains
end
end AspisR19.TwoSwapDomainProbability
