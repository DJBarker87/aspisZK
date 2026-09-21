import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Small-block determinant gate. The concrete permutation, zero pattern,
and identification with the checked block leaves are explicit obligations. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F I J : Type*} [CommRing F] [IsDomain F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem two_block_det_ne_zero (A : Matrix I I F) (B : Matrix I J F)
    (D : Matrix J J F) (ha : A.det ≠ 0) (hd : D.det ≠ 0) :
    (Matrix.fromBlocks A B 0 D).det ≠ 0 := by
  rw [Matrix.det_fromBlocks_zero₂₁]
  exact mul_ne_zero ha hd

theorem row_permuted_det_ne_zero (M : Matrix I I F)
    (rows : Equiv.Perm I) (h : (M.submatrix rows id).det ≠ 0) :
    M.det ≠ 0 := by
  intro hz
  apply h
  rw [Matrix.det_permute, hz, mul_zero]

/-- In particular, a nonzero evaluated determinant witnesses a nonzero
polynomial determinant. Evaluation/source identification is a separate gate. -/
theorem det_ne_zero_of_mapped {R : Type*} [CommRing R]
    (f : R →+* F) (M : Matrix I I R) (h : (f.mapMatrix M).det ≠ 0) : M.det ≠ 0 := by
  rw [← f.map_det] at h
  intro hz
  exact h (by rw [hz, map_zero])

#print axioms det_ne_zero_of_mapped
#print axioms two_block_det_ne_zero
#print axioms row_permuted_det_ne_zero
end AspisV8R17
