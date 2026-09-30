import AspisV8R19.TwoSwapResidualNonzero
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-! Exact fixed-root exceptional-set bound for the two-swap residual minor.

This theorem deliberately keeps the 22 query roots fixed.  It supplies the
algebraic/probability half needed after an actual-source first-read theorem has
justified that the earlier QM31 challenges retain their product-uniform law.
It does not condition on future roots and does not assert that source premise. -/
set_option autoImplicit false
namespace AspisR19.TwoSwapFixedRootProbability
open MvPolynomial AspisV8R15.ExactTowerBase QM31ResidualWitness
open TwoSwapResidualPolynomial TwoSwapResidualNonzero
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

def determinantFor (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) : MvPolynomial (Fin 36) QM31Exact :=
  (polynomial (embed RootCertificate.half) (embed 536870912)
    (TwoSwapResidualSource.querySection t ht noneOne)).det

theorem determinant_ne_zero (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) : determinantFor t ht noneOne ≠ 0 :=
  polynomial_ne_zero embed t ht noneOne

theorem determinant_degree (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) : (determinantFor t ht noneOne).totalDegree ≤ 819 :=
  TwoSwapResidualDegree.determinant_degree _ _ _

theorem cm31_card : Fintype.card CM31Exact = P ^ 2 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd (-1 : M31Exact) 0),
    Fintype.card_prod]
  simp [P,pow_two]

theorem qm31_card : Fintype.card QM31Exact = P ^ 4 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd qm31R 0),Fintype.card_prod,
    cm31_card]
  ring

theorem bad_fraction_le (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) :
    ((Finset.filter (fun s => eval s (determinantFor t ht noneOne) = 0)
        (Fintype.piFinset (fun _ : Fin 36 ↦ (Finset.univ : Finset QM31Exact)))).card : ℚ≥0) /
        ((Finset.univ : Finset QM31Exact).card ^ 36 : ℚ≥0) ≤
      (819 : ℚ≥0) / (Finset.univ : Finset QM31Exact).card := by
  apply (schwartz_zippel_totalDegree (determinant_ne_zero t ht noneOne)
    (Finset.univ : Finset QM31Exact)).trans
  gcongr
  exact_mod_cast determinant_degree t ht noneOne

theorem bad_fraction_le_explicit (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) :
    ((Finset.filter (fun s => eval s (determinantFor t ht noneOne) = 0)
        (Fintype.piFinset (fun _ : Fin 36 ↦ (Finset.univ : Finset QM31Exact)))).card : ℚ≥0) /
        ((↑(P ^ 4) : ℚ≥0) ^ 36) ≤ (819 : ℚ≥0) / (↑(P ^ 4) : ℚ≥0) := by
  simpa only [Finset.card_univ,qm31_card] using bad_fraction_le t ht noneOne

#print axioms determinant_ne_zero
#print axioms determinant_degree
#print axioms cm31_card
#print axioms qm31_card
#print axioms bad_fraction_le
#print axioms bad_fraction_le_explicit
end
end AspisR19.TwoSwapFixedRootProbability
