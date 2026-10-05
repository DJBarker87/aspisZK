import AspisV8R19.R826JointCombinationObservation
import AspisV8R19.R739AugmentedQuery256

set_option autoImplicit false
namespace AspisV8R19.R830JointCombinationTail
open AspisV8R19.R826JointCombinationObservation
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R710SelectedActivePolynomial
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R739AugmentedQuery256
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]
abbrev ObservationRow := R738JointObservationModel.ObservationRow

theorem selected_column_lt94 (col : ObservationRow) : (selectedColumns col).1.val < 94 := by
  rcases col with j | ⟨p | k⟩
  · simp only [selectedColumns]
    have h := (columnIndex j).isLt
    omega
  · simp [selectedColumns]
  · fin_cases k <;> simp [selectedColumns]

theorem combination_tail (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : ObservationRow → F) (i : Fin 256) (hi : 94 ≤ i.val) (slot : Fin 4) :
    combination alpha t ht noneOne x (i,slot) = 0 := by
  unfold combination
  apply Finset.sum_eq_zero
  intro col _
  have hc : (selectedColumns col).1.val < 94 := selected_column_lt94 col
  have hne : i ≠ cast255 (selectedColumns col).1 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [cast255] at hv
    omega
  have hn : normalized t ht noneOne (cast255 (selectedColumns col).1) i = 0 := by
    rw [normalized_high t ht noneOne _ i (by omega)]
    simp [hne]
  unfold normalizedPair
  rw [hn]
  ring

#print axioms selected_column_lt94
#print axioms combination_tail
end
end AspisV8R19.R830JointCombinationTail
