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

/-- Independent row and column reorderings preserve nonvanishing. -/
theorem independently_reindexed_det_ne_zero (M : Matrix I I F)
    (rows cols : J ≃ I) (h : (M.submatrix rows cols).det ≠ 0) : M.det ≠ 0 := by
  have he : M.submatrix rows cols = M.reindex rows.symm cols.symm := rfl
  rw [he, Matrix.det_reindex] at h
  intro hz
  exact h (by rw [hz, mul_zero])

/-- A recursive certificate step with explicit entrywise source obligations.
No determinant expansion is used, regardless of the size of the tail. -/
theorem split_source_det_ne_zero {K : Type*} [Fintype K] [DecidableEq K]
    (M : Matrix I I F) (rows cols : (J ⊕ K) ≃ I)
    (A : Matrix J J F) (D : Matrix K K F)
    (ha : A.det ≠ 0) (hd : D.det ≠ 0)
    (haa : ∀ i j, M (rows (.inl i)) (cols (.inl j)) = A i j)
    (hdd : ∀ i j, M (rows (.inr i)) (cols (.inr j)) = D i j)
    (hzero : ∀ i j, M (rows (.inr i)) (cols (.inl j)) = 0) : M.det ≠ 0 := by
  apply independently_reindexed_det_ne_zero M rows cols
  let B : Matrix J K F := fun i j => M (rows (.inl i)) (cols (.inr j))
  have he : M.submatrix rows cols = Matrix.fromBlocks A B 0 D := by
    ext i j
    cases i <;> cases j
    · exact haa _ _
    · rfl
    · exact hzero _ _
    · exact hdd _ _
  rw [he]
  exact two_block_det_ne_zero A B D ha hd

#print axioms independently_reindexed_det_ne_zero
#print axioms split_source_det_ne_zero
#print axioms det_ne_zero_of_mapped
#print axioms two_block_det_ne_zero
#print axioms row_permuted_det_ne_zero
end AspisV8R17
