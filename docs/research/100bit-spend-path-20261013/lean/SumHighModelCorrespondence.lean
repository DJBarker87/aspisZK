import SumHighInnerLoop
import R0P.Path

/-! Symbolic closed form for the source left-associated high-selector fold,
then correspondence with the existing retained sum_high mathematical model. -/
set_option autoImplicit false
namespace AspisR1.SumHighModelCorrespondence
noncomputable section
open scoped BigOperators
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SumHighInnerLoop

theorem sumModel_eq_sum (selectors : Selectors) (count start : Nat) (acc : ExactQM) :
    sumModel selectors count start acc =
      acc + ∑ i : Fin count, highAt selectors (start + i.val) := by
  induction count generalizing start acc with
  | zero => simp [sumModel]
  | succ count ih =>
      rw [sumModel, ih, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
      have hterms : (∑ i : Fin count, highAt selectors (start + 1 + i.val)) =
          ∑ i : Fin count, highAt selectors (start + (i.val + 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        omega
      rw [hterms, add_assoc]

theorem sumModel_eq_g2SumHigh (selectors : Selectors) (sel : R0P.Sel ExactQM)
    (count start : Nat) (bound : start + count ≤ 64)
    (hhigh : ∀ h : Fin 64, highAt selectors h.val = R0P.g2High sel h) :
    sumModel selectors count start 0 = R0P.g2SumHigh sel start count bound := by
  rw [sumModel_eq_sum, zero_add]
  simp only [R0P.g2SumHigh, R0P.g2_fold_add, zero_add, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact hhigh ⟨start + i.val, by omega⟩

#print axioms sumModel_eq_sum
#print axioms sumModel_eq_g2SumHigh
end
end AspisR1.SumHighModelCorrespondence
