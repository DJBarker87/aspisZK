import AspisV8R19.R833RootFixedJointPolynomial
import AspisV8R17.MinorDegree

set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R834NormalizedJointDegree
open MvPolynomial
open AspisV8R17
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R746SelectedJointMinor
open AspisV8R19.R767NormalizedSparseEntry
open AspisV8R19.R739AugmentedQuery256
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R833RootFixedJointPolynomial
noncomputable section

variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem rootFixedEntry_totalDegree_le (half quarter : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) (D : Nat)
    (hraw : ∀ (d : Fin 255) (s : Fin 3) (row : Obs),
      (polynomialEntry half quarter d s row).totalDegree ≤ D)
    (row col : Obs) :
    (rootFixedEntry half quarter t ht noneOne row col).totalDegree ≤ D := by
  unfold rootFixedEntry
  have hcorrection :
      (∑ j : Fin 23, C (low t ht noneOne (cast255 (selectedColumns col).1) j) *
        polynomialEntry half quarter (⟨j.val, by omega⟩ : Fin 255)
          (selectedColumns col).2 row).totalDegree ≤ D := by
    apply totalDegree_finsetSum_le
    intro j hj
    have hcoeff :
        (C (low t ht noneOne (cast255 (selectedColumns col).1) j) : JointPoly F).totalDegree ≤ 0 := by
      simp
    have hentry := hraw (⟨j.val, by omega⟩ : Fin 255) (selectedColumns col).2 row
    have hmul := totalDegree_mul
      (C (low t ht noneOne (cast255 (selectedColumns col).1) j) : JointPoly F)
      (polynomialEntry half quarter (⟨j.val, by omega⟩ : Fin 255)
        (selectedColumns col).2 row)
    exact hmul.trans (by simpa using Nat.add_le_add hcoeff hentry)
  exact (totalDegree_sub _ _).trans
    (max_le (hraw (selectedColumns col).1 (selectedColumns col).2 row) hcorrection)

theorem rootFixedMatrix_entry_totalDegree_le (half quarter : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) (D : Nat)
    (hraw : ∀ (d : Fin 255) (s : Fin 3) (row : Obs),
      (polynomialEntry half quarter d s row).totalDegree ≤ D)
    (row col : Obs) :
    (rootFixedMatrix half quarter t ht noneOne row col).totalDegree ≤ D := by
  exact rootFixedEntry_totalDegree_le half quarter t ht noneOne D hraw row col

theorem rootFixedMatrix_det_totalDegree_le (half quarter : F) (t : Fin 22 → F)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) (D : Nat)
    (hraw : ∀ (d : Fin 255) (s : Fin 3) (row : Obs),
      (polynomialEntry half quarter d s row).totalDegree ≤ D) :
    (rootFixedMatrix half quarter t ht noneOne).det.totalDegree ≤ 222 * D := by
  have hdet := AspisV8R17.minor_totalDegree
    (rootFixedMatrix half quarter t ht noneOne) D
    (fun i j => rootFixedMatrix_entry_totalDegree_le half quarter t ht noneOne D hraw i j)
  have hcard : Fintype.card Obs = 222 := observation_card
  rw [hcard] at hdet
  exact hdet

#print axioms rootFixedEntry_totalDegree_le
#print axioms rootFixedMatrix_entry_totalDegree_le
#print axioms rootFixedMatrix_det_totalDegree_le
end
end AspisV8R19.R834NormalizedJointDegree
