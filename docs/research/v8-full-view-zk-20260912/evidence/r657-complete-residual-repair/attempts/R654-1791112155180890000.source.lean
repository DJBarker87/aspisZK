import AspisV8R19.R649TwoSwapResidualRepair

/-! A nonzero exact selected residual determinant excludes alpha zero. This
uses only the explicit query-table hypotheses; it is not a sampling law. -/
set_option autoImplicit false
namespace AspisV8R19.R654ResidualAlphaNonzero

open AspisV8R17
open AspisR19 AspisR19.HighRepairInvariant AspisR19.NormalizedGCore
open AspisR19.TwoSwapWitness
open AspisV8R19.R649TwoSwapResidualRepair
open scoped BigOperators

noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

private theorem selected_slot_nonzero (j : Fin 13) :
    TwoSwapWitness.slot j ≠ 0 := by
  fin_cases j <;> decide

private theorem selected_slotFactor_zero (j : Fin 13) :
    NormalizedQuotient.slotFactor (0 : F) (TwoSwapWitness.slot j) 0 = 0 := by
  unfold NormalizedQuotient.slotFactor
  have hs := selected_slot_nonzero j
  have hp : 0 < (TwoSwapWitness.slot j).val := by
    have := (TwoSwapWitness.slot j).isLt
    by_contra hn
    have hz : (TwoSwapWitness.slot j).val = 0 := by omega
    apply hs
    exact Fin.ext hz
  simp [hs, pow_eq_zero_of_pos hp]

private theorem selected_slot_zero (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (j : Fin 13) (d : Fin 32) :
    AugmentedQuotient.quotient t ht noneOne 0
      (TwoSwapWitness.degree j) (TwoSwapWitness.slot j) (d,0) = 0 := by
  unfold AugmentedQuotient.quotient AugmentedQuotient.lift
  rw [selected_slotFactor_zero]
  ring

private theorem coefficient_zero_of_slot_zero (quarter : F)
    (q w : Index 32 → F) (hq : ∀ d : Fin 32, q (d,0) = 0) :
    coefficient (sourceKernel 32 0 quarter) q w = 0 := by
  rw [FullCoefficientBoundary.coefficient_blocks]
  apply Finset.sum_eq_zero
  intro d _
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro u _
  by_cases h : s.val + (4-u.val)%4 = 0
  · have hs : s = 0 := by
      apply Fin.ext
      omega
    subst s
    simp only [if_pos h, hq, mul_zero, zero_mul]
  · simp [h]

private theorem observed_row_three_zero (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (half quarter a b c kappa tau : F) (z : Fin 10 → F)
    (previous : Fin 271 → F) (j : Fin 13) :
    TwoSwapResidualSource.observed half quarter a b c kappa tau z previous
      (AugmentedQuotient.quotient t ht noneOne 0
        (TwoSwapWitness.degree j) (TwoSwapWitness.slot j)) 3 = 0 := by
  unfold TwoSwapResidualSource.observed
  simp only [show ¬3 < 3 by omega, show 3 < 10 by omega, ↓reduceIte]
  rw [TwoSwapResidualSource.relation_eq]
  apply coefficient_zero_of_slot_zero
  exact selected_slot_zero t ht noneOne j

theorem residual_matrix_alpha_ne_zero (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (half quarter a b c kappa alpha tau : F) (z : Fin 10 → F)
    (previous : Fin 271 → F)
    (hdet : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z
      previous t ht noneOne).det ≠ 0) : alpha ≠ 0 := by
  intro ha
  subst alpha
  apply hdet
  apply Matrix.det_eq_zero_of_row_eq_zero (2 : Fin 13)
  intro j
  unfold TwoSwapResidualSource.matrix
  change TwoSwapResidualSource.observed half quarter a b c kappa tau z previous
    (AugmentedQuotient.quotient t ht noneOne 0
      (TwoSwapWitness.degree j) (TwoSwapWitness.slot j)) 3 = 0
  exact observed_row_three_zero t ht noneOne half quarter a b c kappa tau z previous j

#print axioms residual_matrix_alpha_ne_zero

end
end AspisV8R19.R654ResidualAlphaNonzero
