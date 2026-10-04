import Mathlib.LinearAlgebra.Matrix.Block
import AspisV8R19.R766BlockOrderEquivalences

set_option autoImplicit false
namespace AspisV8R19.R805BlockDeterminantAssembly
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

theorem blockTriangular_det_isUnit (A : Matrix m m R) (label : m → ι)
    (htri : A.BlockTriangular label)
    (hdiag : ∀ k : ι, IsUnit (A.toSquareBlock label k).det) : IsUnit A.det := by
  rw [htri.det_fintype]
  exact IsUnit.prod_univ_iff.mpr hdiag

theorem permuted_det_isUnit_iff (A : Matrix m m R) (rows cols : m ≃ m) :
    IsUnit (A.submatrix rows cols).det ↔ IsUnit A.det := by
  rw [Matrix.det_submatrix_equiv_equiv]
  simp

#print axioms blockTriangular_det_isUnit
#print axioms permuted_det_isUnit_iff
end
end AspisV8R19.R805BlockDeterminantAssembly
