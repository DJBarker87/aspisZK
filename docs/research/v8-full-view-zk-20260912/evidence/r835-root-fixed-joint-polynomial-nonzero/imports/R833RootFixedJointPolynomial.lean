import Mathlib.Algebra.MvPolynomial.Eval
import AspisV8R19.R745JointObservationPolynomial
import AspisV8R19.R767NormalizedSparseEntry
import AspisV8R19.R781NormalizedActivePreservation

/-! The R745 selected polynomial matrix after fixing the query-normalization
coefficients as coefficient-ring constants. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R833RootFixedJointPolynomial
open MvPolynomial
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R767NormalizedSparseEntry
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R765NormalizedJointRepair
open AspisV8R19.R739AugmentedQuery256
open AspisV8R19.R741SparseCoefficientObservation
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [NeZero (2 : F)]
abbrev Obs := R738JointObservationModel.ObservationRow

def rootFixedEntry (half quarter : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1)
    (row col : Obs) : JointPoly F :=
  polynomialEntry half quarter (selectedColumns col).1 (selectedColumns col).2 row -
    ∑ j : Fin 23, C (low t ht noneOne (cast255 (selectedColumns col).1) j) *
      polynomialEntry half quarter
        (⟨j.val, by omega⟩ : Fin 255) (selectedColumns col).2 row

def rootFixedMatrix (half quarter : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    Matrix Obs Obs (JointPoly F) :=
  fun row col => rootFixedEntry half quarter t ht noneOne row col

theorem eval_rootFixedEntry (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (row col : Obs) :
    eval (assignment alpha u v kappa tau z)
      (rootFixedEntry half quarter t ht noneOne row col) =
      rawObservation half quarter (1 + u*v) (u*v-1) (-(u+v)) kappa tau z
        (normalizedPair alpha t ht noneOne
          (cast255 (selectedColumns col).1) (selectedColumns col).2) row := by
  unfold rootFixedEntry
  rw [map_sub, map_sum]
  simp only [eval_C, map_mul]
  rw [eval_polynomialEntry]
  simp_rw [eval_polynomialEntry]
  rw [rawObservation_indexedDirection]
  simp_rw [rawObservation_indexedDirection]
  exact (normalized_sparse_entry half quarter (1 + u*v) (u*v-1) (-(u+v))
    kappa tau alpha z row t ht noneOne (selectedColumns col).1
    (selectedColumns col).2).symm

theorem eval_rootFixedMatrix (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) :
    (eval (assignment alpha u v kappa tau z)).mapMatrix
      (rootFixedMatrix half quarter t ht noneOne) =
      normalizedSelectedMatrix half quarter alpha u v kappa tau z t ht noneOne := by
  ext row col
  exact eval_rootFixedEntry half quarter alpha u v kappa tau z t ht noneOne row col

theorem eval_rootFixedMatrix_det [Fintype Obs] [DecidableEq Obs]
    (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) :
    eval (assignment alpha u v kappa tau z)
      (rootFixedMatrix half quarter t ht noneOne).det =
      (normalizedSelectedMatrix half quarter alpha u v kappa tau z t ht noneOne).det := by
  rw [(eval (assignment alpha u v kappa tau z)).map_det]
  exact congrArg Matrix.det
    (eval_rootFixedMatrix half quarter alpha u v kappa tau z t ht noneOne)

#print axioms eval_rootFixedEntry
#print axioms eval_rootFixedMatrix
#print axioms eval_rootFixedMatrix_det
end
end AspisV8R19.R833RootFixedJointPolynomial
