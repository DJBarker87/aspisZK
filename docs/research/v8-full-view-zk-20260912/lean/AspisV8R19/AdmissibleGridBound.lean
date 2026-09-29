/- Finite uniform-grid bounds. This file does not assert a source sampler law. -/
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

namespace AspisR19.AdmissibleGridBound
open Finset Fintype
noncomputable section
variable {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]

theorem mixed_grid {n : Nat} (p : MvPolynomial (Fin n) F) (hp : p ≠ 0)
    (S : Fin n → Finset F) (m d : Nat) (hm : 0 < m)
    (hS : ∀ i, m ≤ (S i).card) (hd : p.totalDegree ≤ d) :
    ((piFinset S).filter (fun x => MvPolynomial.eval x p = 0)).card /
        (∏ i, ((S i).card : ℚ≥0)) ≤ (d : ℚ≥0) / m := by
  refine (MvPolynomial.schwartz_zippel_sup_sum hp S).trans ?_
  apply Finset.sup_le
  intro s hs
  calc
    (∑ i, (s i : ℚ≥0) / (S i).card) ≤ ∑ i, (s i : ℚ≥0) / m := by
      apply Finset.sum_le_sum
      intro i _
      exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hm)
        (by exact_mod_cast hS i)
    _ = (∑ i, (s i : ℚ≥0)) / m := (Finset.sum_div _ _ _).symm
    _ ≤ (d : ℚ≥0) / m := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hsdegree : (∑ i, s i) ≤ p.totalDegree := by
        simpa [Finsupp.sum_fintype] using MvPolynomial.le_totalDegree hs
      exact_mod_cast hsdegree.trans hd

theorem restrict_uniform {A : Type*} [DecidableEq A]
    (grid admitted : Finset A) (bad : A → Prop) [DecidablePred bad]
    (hsub : admitted ⊆ grid) (hgrid : grid.Nonempty) (hadm : admitted.Nonempty)
    (b : ℚ≥0) (hbad : ((grid.filter bad).card : ℚ≥0) / grid.card ≤ b) :
    ((admitted.filter bad).card : ℚ≥0) / admitted.card ≤
      b / ((admitted.card : ℚ≥0) / grid.card) := by
  have hg : (0 : ℚ≥0) < grid.card := by exact_mod_cast hgrid.card_pos
  have ha : (0 : ℚ≥0) < admitted.card := by exact_mod_cast hadm.card_pos
  have hc : ((admitted.filter bad).card : ℚ≥0) ≤ (grid.filter bad).card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter bad hsub)
  have hnum := (div_le_iff₀ hg).mp hbad
  rw [div_div_eq_mul_div]
  exact (div_le_div_iff_of_pos_right ha).mpr (hc.trans hnum)

theorem admitted_grid {n : Nat} (p : MvPolynomial (Fin n) F) (hp : p ≠ 0)
    (S : Fin n → Finset F) (admitted : Finset (Fin n → F))
    (hsub : admitted ⊆ piFinset S) (hadm : admitted.Nonempty)
    (m d : Nat) (hm : 0 < m) (hS : ∀ i, m ≤ (S i).card)
    (hd : p.totalDegree ≤ d) :
    ((admitted.filter (fun x => MvPolynomial.eval x p = 0)).card : ℚ≥0) /
        admitted.card ≤
      ((d : ℚ≥0) / m) / ((admitted.card : ℚ≥0) / (piFinset S).card) := by
  apply restrict_uniform (piFinset S) admitted _ hsub (hadm.mono hsub) hadm
  simpa only [Fintype.card_piFinset, Nat.cast_prod] using mixed_grid p hp S m d hm hS hd

#print axioms mixed_grid
#print axioms restrict_uniform
#print axioms admitted_grid
end
end AspisR19.AdmissibleGridBound
