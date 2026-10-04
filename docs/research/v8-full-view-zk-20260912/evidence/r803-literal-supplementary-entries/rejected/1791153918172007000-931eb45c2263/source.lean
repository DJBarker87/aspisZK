import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R802OrdinaryDirectionPointCoefficients
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R803LiteralSupplementaryEntries
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R802OrdinaryDirectionPointCoefficients
noncomputable section

def pointPosition (p : Fin 3) : Fin 222 := ⟨214+p.val, by omega⟩
def coefficientPosition (k : Fin 5) : Fin 222 := ⟨217+k.val, by omega⟩

theorem sourceView_pointPosition (p : Fin 3) :
    sourceView (pointPosition p) = .inr (.inl p) := by
  fin_cases p <;> rfl

theorem sourceView_coefficientPosition (k : Fin 5) :
    sourceView (coefficientPosition k) = .inr (.inr k) := by
  fin_cases k <;> rfl

variable {F : Type*} [CommRing F] [Nontrivial F]
theorem literalSourceMatrix_point_entry (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (p : Fin 3) (j : Fin 222) :
    literalSourceMatrix half quarter alpha u v kappa tau z (pointPosition p) j =
      sparseObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau alpha z
        (columnView j).1 (columnView j).2 (.inr (.inl p)) := by
  rw [literalSourceMatrix_entry, sourceView_pointPosition]
  exact congrFun (rawObservation_indexedDirection half quarter (1+u*v) (u*v-1)
    (-(u+v)) kappa tau alpha z (columnView j).1 (columnView j).2) (.inr (.inl p))

theorem literalSourceMatrix_coefficient_entry (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (k : Fin 5) (j : Fin 222) :
    literalSourceMatrix half quarter alpha u v kappa tau z (coefficientPosition k) j =
      kappa * pointCoefficient half quarter (1+u*v) (u*v-1) (-(u+v))
        (SourceStatementPoints.points z 0)
        (indexedDirection alpha (columnView j).1 (columnView j).2) (relationIndex k) +
      kappa^2 * pointCoefficient half quarter (1+u*v) (u*v-1) (-(u+v))
        (SourceStatementPoints.points z 1)
        (indexedDirection alpha (columnView j).1 (columnView j).2) (relationIndex k) +
      kappa^3 * pointCoefficient half quarter (1+u*v) (u*v-1) (-(u+v))
        (SourceStatementPoints.points z 2)
        (indexedDirection alpha (columnView j).1 (columnView j).2) (relationIndex k) := by
  rw [literalSourceMatrix_entry, sourceView_coefficientPosition]
  change rawRelation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
    (indexedDirection alpha (columnView j).1 (columnView j).2) (relationIndex k) = _
  exact rawRelation_direction_point_decomposition half quarter (1+u*v) (u*v-1)
    (-(u+v)) alpha kappa tau z (columnView j).1 (columnView j).2 (relationIndex k)

#print axioms sourceView_pointPosition
#print axioms sourceView_coefficientPosition
#print axioms literalSourceMatrix_point_entry
#print axioms literalSourceMatrix_coefficient_entry
end
end AspisV8R19.R803LiteralSupplementaryEntries
