import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks00
import AspisV8R17.SourceDiagonalBlocks01
import AspisV8R17.SourceDiagonalBlocks02
import AspisV8R17.SourceDiagonalBlocks05
import AspisV8R17.SourceLowerBlocks00
import AspisV8R17.SourceLowerBlocks01
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block0_eq : matrixWindow sourceMatrix 0 1 = BlockDeterminants.block0 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 0 0 = 1073741827
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block3_entry0_0
theorem block0_unit : IsUnit (matrixWindow sourceMatrix 0 1).det := by
  rw [block0_eq]
  exact BlockDeterminants.block0_det_isUnit
theorem block0_lower : ∀ (i : Fin 213) (j : Fin 1),
    sourceMatrix (0+1+i.val) (0+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (1+i.val) 0 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column5_lower 1073741824 2 13 11 (-7) i
#print axioms block0_eq
#print axioms block0_unit
#print axioms block0_lower

theorem block1_eq : matrixWindow sourceMatrix 1 2 = BlockDeterminants.block3 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 1 1 = 234881024
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block4_entry0_0
    ·
      change sourceMatrix 1 2 = 369098752
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block4_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 2 1 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block4_entry1_0
    ·
      change sourceMatrix 2 2 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block4_entry1_1
theorem block1_unit : IsUnit (matrixWindow sourceMatrix 1 2).det := by
  rw [block1_eq]
  exact BlockDeterminants.block3_det_isUnit
theorem block1_lower : ∀ (i : Fin 211) (j : Fin 2),
    sourceMatrix (1+2+i.val) (1+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (3+i.val) 1 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column6_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (3+i.val) 2 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column7_lower 1073741824 2 13 11 (-7) i
#print axioms block1_eq
#print axioms block1_unit
#print axioms block1_lower

theorem block2_eq : matrixWindow sourceMatrix 3 2 = BlockDeterminants.block9 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 3 3 = 469762048
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block12_entry0_0
    ·
      change sourceMatrix 3 4 = 738197504
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block12_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 4 3 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block12_entry1_0
    ·
      change sourceMatrix 4 4 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block12_entry1_1
theorem block2_unit : IsUnit (matrixWindow sourceMatrix 3 2).det := by
  rw [block2_eq]
  exact BlockDeterminants.block9_det_isUnit
theorem block2_lower : ∀ (i : Fin 209) (j : Fin 2),
    sourceMatrix (3+2+i.val) (3+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (5+i.val) 3 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column20_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (5+i.val) 4 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column21_lower 1073741824 2 13 11 (-7) i
#print axioms block2_eq
#print axioms block2_unit
#print axioms block2_lower

theorem block3_eq : matrixWindow sourceMatrix 5 1 = BlockDeterminants.block14 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 5 5 = 117440512
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block21_entry0_0
theorem block3_unit : IsUnit (matrixWindow sourceMatrix 5 1).det := by
  rw [block3_eq]
  exact BlockDeterminants.block14_det_isUnit
theorem block3_lower : ∀ (i : Fin 208) (j : Fin 1),
    sourceMatrix (5+1+i.val) (5+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (6+i.val) 5 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column35_lower 1073741824 2 13 11 (-7) i
#print axioms block3_eq
#print axioms block3_unit
#print axioms block3_lower

theorem block4_eq : matrixWindow sourceMatrix 6 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 6 6 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block53_entry0_0
    ·
      change sourceMatrix 6 7 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block53_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 7 6 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block53_entry1_0
    ·
      change sourceMatrix 7 7 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block53_entry1_1
theorem block4_unit : IsUnit (matrixWindow sourceMatrix 6 2).det := by
  rw [block4_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block4_lower : ∀ (i : Fin 206) (j : Fin 2),
    sourceMatrix (6+2+i.val) (6+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (8+i.val) 6 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column85_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (8+i.val) 7 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column86_lower 1073741824 2 13 11 (-7) i
#print axioms block4_eq
#print axioms block4_unit
#print axioms block4_lower

theorem block5_eq : matrixWindow sourceMatrix 8 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 8 8 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block52_entry0_0
theorem block5_unit : IsUnit (matrixWindow sourceMatrix 8 1).det := by
  rw [block5_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block5_lower : ∀ (i : Fin 205) (j : Fin 1),
    sourceMatrix (8+1+i.val) (8+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (9+i.val) 8 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column84_lower 1073741824 2 13 11 (-7) i
#print axioms block5_eq
#print axioms block5_unit
#print axioms block5_lower

theorem block6_eq : matrixWindow sourceMatrix 9 1 = BlockDeterminants.block23 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 9 9 = 58720256
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block54_entry0_0
theorem block6_unit : IsUnit (matrixWindow sourceMatrix 9 1).det := by
  rw [block6_eq]
  exact BlockDeterminants.block23_det_isUnit
theorem block6_lower : ∀ (i : Fin 204) (j : Fin 1),
    sourceMatrix (9+1+i.val) (9+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (10+i.val) 9 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column87_lower 1073741824 2 13 11 (-7) i
#print axioms block6_eq
#print axioms block6_unit
#print axioms block6_lower

theorem block7_eq : matrixWindow sourceMatrix 10 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 10 10 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block57_entry0_0
    ·
      change sourceMatrix 10 11 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block57_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 11 10 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block57_entry1_0
    ·
      change sourceMatrix 11 11 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block57_entry1_1
theorem block7_unit : IsUnit (matrixWindow sourceMatrix 10 2).det := by
  rw [block7_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block7_lower : ∀ (i : Fin 202) (j : Fin 2),
    sourceMatrix (10+2+i.val) (10+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (12+i.val) 10 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column90_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (12+i.val) 11 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column91_lower 1073741824 2 13 11 (-7) i
#print axioms block7_eq
#print axioms block7_unit
#print axioms block7_lower

end AspisV8R17.SourceMinor.Windows
