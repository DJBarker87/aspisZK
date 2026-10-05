import AspisV8R19.R781NormalizedActivePreservation
import AspisV8R19.R764RawJointWeights

set_option autoImplicit false
namespace AspisV8R19.R826JointCombinationObservation
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R764RawJointWeights
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

abbrev ObservationRow := R738JointObservationModel.ObservationRow

def combination (alpha : F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (x : ObservationRow → F) : R738JointObservationModel.Index256 → F :=
  fun i => ∑ col : ObservationRow,
    x col * normalizedPair alpha t ht noneOne
      (cast255 (selectedColumns col).1) (selectedColumns col).2 i

theorem combination_observation (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (x : ObservationRow → F) (row : ObservationRow) :
    rawObservation half quarter (1 + u*v) (u*v - 1) (-(u+v)) kappa tau z
      (combination alpha t ht noneOne x) row =
      (normalizedSelectedMatrix half quarter alpha u v kappa tau z t ht noneOne).mulVec x row := by
  rw [rawObservation_weighted]
  unfold combination Matrix.mulVec normalizedSelectedMatrix
  simp only [Pi.sum_apply]
  simp only [rawObservation_weighted]
  rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro col _
  rw [← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

#print axioms combination_observation
end
end AspisV8R19.R826JointCombinationObservation
