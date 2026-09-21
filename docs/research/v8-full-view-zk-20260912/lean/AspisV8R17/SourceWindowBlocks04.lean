import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks07
import AspisV8R17.SourceLowerBlocks06
import AspisV8R17.SourceLowerBlocks07
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block32_eq : matrixWindow sourceMatrix 48 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 48 48 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block80_entry0_0
theorem block32_unit : IsUnit (matrixWindow sourceMatrix 48 1).det := by
  rw [block32_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block32_lower : ∀ (i : Fin 165) (j : Fin 1),
    sourceMatrix (48+1+i.val) (48+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (49+i.val) 48 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column125_lower 1073741824 2 13 11 (-7) i
#print axioms block32_eq
#print axioms block32_unit
#print axioms block32_lower

theorem block33_eq : matrixWindow sourceMatrix 49 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 49 49 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block83_entry0_0
    ·
      change sourceMatrix 49 50 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block83_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 50 49 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block83_entry1_0
    ·
      change sourceMatrix 50 50 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block83_entry1_1
theorem block33_unit : IsUnit (matrixWindow sourceMatrix 49 2).det := by
  rw [block33_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block33_lower : ∀ (i : Fin 163) (j : Fin 2),
    sourceMatrix (49+2+i.val) (49+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (51+i.val) 49 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column129_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (51+i.val) 50 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column130_lower 1073741824 2 13 11 (-7) i
#print axioms block33_eq
#print axioms block33_unit
#print axioms block33_lower

theorem block34_eq : matrixWindow sourceMatrix 51 1 = BlockDeterminants.block24 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 51 51 = 939524096
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block82_entry0_0
theorem block34_unit : IsUnit (matrixWindow sourceMatrix 51 1).det := by
  rw [block34_eq]
  exact BlockDeterminants.block24_det_isUnit
theorem block34_lower : ∀ (i : Fin 162) (j : Fin 1),
    sourceMatrix (51+1+i.val) (51+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (52+i.val) 51 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column128_lower 1073741824 2 13 11 (-7) i
#print axioms block34_eq
#print axioms block34_unit
#print axioms block34_lower

theorem block35_eq : matrixWindow sourceMatrix 52 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 52 52 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block85_entry0_0
    ·
      change sourceMatrix 52 53 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block85_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 53 52 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block85_entry1_0
    ·
      change sourceMatrix 53 53 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block85_entry1_1
theorem block35_unit : IsUnit (matrixWindow sourceMatrix 52 2).det := by
  rw [block35_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block35_lower : ∀ (i : Fin 160) (j : Fin 2),
    sourceMatrix (52+2+i.val) (52+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (54+i.val) 52 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column132_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (54+i.val) 53 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column133_lower 1073741824 2 13 11 (-7) i
#print axioms block35_eq
#print axioms block35_unit
#print axioms block35_lower

theorem block36_eq : matrixWindow sourceMatrix 54 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 54 54 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block84_entry0_0
theorem block36_unit : IsUnit (matrixWindow sourceMatrix 54 1).det := by
  rw [block36_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block36_lower : ∀ (i : Fin 159) (j : Fin 1),
    sourceMatrix (54+1+i.val) (54+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (55+i.val) 54 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column131_lower 1073741824 2 13 11 (-7) i
#print axioms block36_eq
#print axioms block36_unit
#print axioms block36_lower

theorem block37_eq : matrixWindow sourceMatrix 55 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 55 55 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block87_entry0_0
    ·
      change sourceMatrix 55 56 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block87_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 56 55 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block87_entry1_0
    ·
      change sourceMatrix 56 56 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block87_entry1_1
theorem block37_unit : IsUnit (matrixWindow sourceMatrix 55 2).det := by
  rw [block37_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block37_lower : ∀ (i : Fin 157) (j : Fin 2),
    sourceMatrix (55+2+i.val) (55+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (57+i.val) 55 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column135_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (57+i.val) 56 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column136_lower 1073741824 2 13 11 (-7) i
#print axioms block37_eq
#print axioms block37_unit
#print axioms block37_lower

theorem block38_eq : matrixWindow sourceMatrix 57 1 = BlockDeterminants.block14 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 57 57 = 117440512
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block86_entry0_0
theorem block38_unit : IsUnit (matrixWindow sourceMatrix 57 1).det := by
  rw [block38_eq]
  exact BlockDeterminants.block14_det_isUnit
theorem block38_lower : ∀ (i : Fin 156) (j : Fin 1),
    sourceMatrix (57+1+i.val) (57+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (58+i.val) 57 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column134_lower 1073741824 2 13 11 (-7) i
#print axioms block38_eq
#print axioms block38_unit
#print axioms block38_lower

theorem block39_eq : matrixWindow sourceMatrix 58 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 58 58 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block89_entry0_0
    ·
      change sourceMatrix 58 59 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block89_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 59 58 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block89_entry1_0
    ·
      change sourceMatrix 59 59 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block89_entry1_1
theorem block39_unit : IsUnit (matrixWindow sourceMatrix 58 2).det := by
  rw [block39_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block39_lower : ∀ (i : Fin 154) (j : Fin 2),
    sourceMatrix (58+2+i.val) (58+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (60+i.val) 58 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column138_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (60+i.val) 59 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column139_lower 1073741824 2 13 11 (-7) i
#print axioms block39_eq
#print axioms block39_unit
#print axioms block39_lower

end AspisV8R17.SourceMinor.Windows
