import AspisV8R19.R745JointObservationPolynomial
import AspisV8R19.R710SelectedActivePolynomial

/-! The fixed 222-column joint minor schema.  This file only fixes ordering
and evaluation; it makes no rank or nonzero assertion. -/
set_option autoImplicit false
namespace AspisV8R19.R746SelectedJointMinor
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R710SelectedActivePolynomial
open scoped BigOperators
noncomputable section
variable {F : Type*} [CommRing F] [Nontrivial F]

abbrev ObservationRow := R738JointObservationModel.ObservationRow
abbrev J := R710SelectedActivePolynomial.J
abbrev Index256 := R738JointObservationModel.Index256

def selectedColumns : ObservationRow → Fin 255 × Fin 3
  | .inl j =>
      (⟨22 + (columnIndex j).val / 3, by
          have h := (columnIndex j).isLt
          omega⟩,
       ⟨(columnIndex j).val % 3, Nat.mod_lt _ (by decide)⟩)
  | .inr (.inl p) => (⟨23, by omega⟩, p)
  | .inr (.inr ⟨0, _⟩) => (⟨24, by omega⟩, ⟨0, by omega⟩)
  | .inr (.inr ⟨1, _⟩) => (⟨24, by omega⟩, ⟨1, by omega⟩)
  | .inr (.inr ⟨2, _⟩) => (⟨24, by omega⟩, ⟨2, by omega⟩)
  | .inr (.inr ⟨3, _⟩) => (⟨27, by omega⟩, ⟨2, by omega⟩)
  | .inr (.inr ⟨4, _⟩) => (⟨47, by omega⟩, ⟨2, by omega⟩)

def selectedPolynomialMatrix (half quarter : F) :
    Matrix ObservationRow ObservationRow (JointPoly F) :=
  polynomialMatrix half quarter selectedColumns

def chosenSourceMatrix (half quarter alpha u v kappa tau : F) (z : Fin 10 → F) :
    Matrix ObservationRow ObservationRow F :=
  fun row col => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
    (indexedDirection alpha (selectedColumns col).1 (selectedColumns col).2) row

theorem selected_matrix_eval (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) :
    (eval (assignment alpha u v kappa tau z)).mapMatrix
      (selectedPolynomialMatrix half quarter) =
      chosenSourceMatrix half quarter alpha u v kappa tau z := by
  exact eval_polynomialMatrix half quarter alpha u v kappa tau z selectedColumns

theorem selected_matrix_det_eval [Fintype ObservationRow] [DecidableEq ObservationRow]
    (half quarter alpha u v kappa tau : F) (z : Fin 10 → F) :
    eval (assignment alpha u v kappa tau z) (selectedPolynomialMatrix half quarter).det =
      (chosenSourceMatrix half quarter alpha u v kappa tau z).det := by
  exact eval_polynomialMatrix_det half quarter alpha u v kappa tau z selectedColumns

theorem observation_card : Fintype.card ObservationRow = 222 := by
  rw [show ObservationRow = J ⊕ (Fin 3 ⊕ Fin 5) by rfl, Fintype.card_sum,
    Fintype.card_sum, index_card]
  norm_num

#print axioms selected_matrix_eval
#print axioms selected_matrix_det_eval
#print axioms observation_card
end
end AspisV8R19.R746SelectedJointMinor
