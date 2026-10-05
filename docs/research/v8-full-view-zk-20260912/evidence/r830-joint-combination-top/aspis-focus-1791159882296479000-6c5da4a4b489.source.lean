import AspisV8R19.R826JointCombinationObservation
import AspisV8R19.R739AugmentedQuery256

set_option autoImplicit false
namespace AspisV8R19.R830JointCombinationTail
open AspisV8R19.R826JointCombinationObservation
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R739AugmentedQuery256
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]
abbrev ObservationRow := R738JointObservationModel.ObservationRow

/-- The selected normalized combination has no degree-255 coordinate.
This is the exact top-four quotient condition after flattening; it does not
assert a tail starting at degree 94. -/
theorem combination_degree255 (alpha : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (x : ObservationRow → F) (slot : Fin 4) :
    combination alpha t ht noneOne x ((255 : Fin 256),slot) = 0 := by
  unfold combination
  apply Finset.sum_eq_zero
  intro col _
  have hne : (255 : Fin 256) ≠ cast255 (selectedColumns col).1 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [cast255] at hv
    have hc := (selectedColumns col).1.isLt
    omega
  have hn : normalized t ht noneOne (cast255 (selectedColumns col).1) (255 : Fin 256) = 0 := by
    rw [normalized_high t ht noneOne _ _ (by omega)]
    simp [hne]
  unfold normalizedPair
  rw [hn]
  ring

#print axioms combination_degree255
end
end AspisV8R19.R830JointCombinationTail
