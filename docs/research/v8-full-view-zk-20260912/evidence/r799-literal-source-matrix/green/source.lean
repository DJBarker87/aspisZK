import AspisV8R19.R798LiteralObservationView
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
namespace AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
noncomputable section
variable {F : Type*} [CommRing F] [Nontrivial F]

def literalSourceMatrix (half quarter alpha u v kappa tau : F) (z : Fin 10 → F) :
    Matrix (Fin 222) (Fin 222) F :=
  (chosenSourceMatrix half quarter alpha u v kappa tau z).submatrix sourceView sourceView

theorem literalSourceMatrix_entry (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (r c : Fin 222) :
    literalSourceMatrix half quarter alpha u v kappa tau z r c =
      rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (indexedDirection alpha (columnView c).1 (columnView c).2) (sourceView r) := by
  change rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
    (indexedDirection alpha (selectedColumns (sourceView c)).1
      (selectedColumns (sourceView c)).2) (sourceView r) = _
  rw [selectedColumns_sourceView]

theorem literalSourceMatrix_det (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) :
    (literalSourceMatrix half quarter alpha u v kappa tau z).det =
      (chosenSourceMatrix half quarter alpha u v kappa tau z).det := by
  exact Matrix.det_submatrix_equiv_self sourceObservationEquiv
    (chosenSourceMatrix half quarter alpha u v kappa tau z)

theorem literalSourceMatrix_det_ne_zero_iff (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) :
    (literalSourceMatrix half quarter alpha u v kappa tau z).det ≠ 0 ↔
      (chosenSourceMatrix half quarter alpha u v kappa tau z).det ≠ 0 := by
  rw [literalSourceMatrix_det]

#print axioms literalSourceMatrix_entry
#print axioms literalSourceMatrix_det
#print axioms literalSourceMatrix_det_ne_zero_iff
end
end AspisV8R19.R799LiteralSourceMatrix
