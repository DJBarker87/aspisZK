import AspisV8R19.R767NormalizedSparseEntry
import AspisV8R19.R773LowActiveKernel
import AspisV8R19.R746SelectedJointMinor
namespace AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R767NormalizedSparseEntry
open AspisV8R19.R746SelectedJointMinor
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem normalized_active_entry (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 255) (s : Fin 3)
    (j : R738JointObservationModel.J) :
    rawObservation half quarter a b c kappa tau z
      (normalizedPair alpha t ht noneOne (cast255 d) s) (.inl j) =
      R743JointSparseEntryBinding.sparseObservation half quarter a b c kappa tau alpha z d s (.inl j) := by
  rw [normalized_sparse_entry]
  have hz (i : Fin 23) : R743JointSparseEntryBinding.sparseObservation
      half quarter a b c kappa tau alpha z ⟨i.val,by omega⟩ s (.inl j) = 0 := by
    exact R773LowActiveKernel.low_active_observation_zero half a b c alpha i s j
  simp only [hz,mul_zero,Finset.sum_const_zero,sub_zero]

def normalizedSelectedMatrix (half quarter alpha u v kappa tau : F) (z : Fin 10 → F)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    Matrix R738JointObservationModel.ObservationRow R738JointObservationModel.ObservationRow F :=
  fun row col => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
    (normalizedPair alpha t ht noneOne (cast255 (selectedColumns col).1) (selectedColumns col).2) row

theorem normalized_selected_active_rows (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (j : R738JointObservationModel.J)
    (col : R738JointObservationModel.ObservationRow) :
    normalizedSelectedMatrix half quarter alpha u v kappa tau z t ht noneOne (.inl j) col =
      chosenSourceMatrix half quarter alpha u v kappa tau z (.inl j) col := by
  unfold normalizedSelectedMatrix chosenSourceMatrix
  rw [normalized_active_entry, R743JointSparseEntryBinding.rawObservation_indexedDirection]

#print axioms normalized_active_entry
#print axioms normalized_selected_active_rows
end
end AspisV8R19.R781NormalizedActivePreservation
