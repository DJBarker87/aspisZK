import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks04
import AspisV8R17.SourceDiagonalBlocks05
import AspisV8R17.SourceLowerBlocks26
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block128_eq : matrixWindow sourceMatrix 209 1 = BlockDeterminants.block21 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 209 209 = 11
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block45_entry0_0
theorem block128_unit : IsUnit (matrixWindow sourceMatrix 209 1).det := by
  rw [block128_eq]
  exact BlockDeterminants.block21_det_isUnit
theorem block128_lower : ∀ (i : Fin 4) (j : Fin 1),
    sourceMatrix (209+1+i.val) (209+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (210+i.val) 209 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column76_lower 1073741824 2 13 11 (-7) i
#print axioms block128_eq
#print axioms block128_unit
#print axioms block128_lower

theorem block129_eq : matrixWindow sourceMatrix 210 1 = BlockDeterminants.block1 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 210 210 = 1073741829
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block47_entry0_0
theorem block129_unit : IsUnit (matrixWindow sourceMatrix 210 1).det := by
  rw [block129_eq]
  exact BlockDeterminants.block1_det_isUnit
theorem block129_lower : ∀ (i : Fin 3) (j : Fin 1),
    sourceMatrix (210+1+i.val) (210+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (211+i.val) 210 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column78_lower 1073741824 2 13 11 (-7) i
#print axioms block129_eq
#print axioms block129_unit
#print axioms block129_lower

theorem block130_eq : matrixWindow sourceMatrix 211 1 = BlockDeterminants.block1 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 211 211 = 1073741829
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block50_entry0_0
theorem block130_unit : IsUnit (matrixWindow sourceMatrix 211 1).det := by
  rw [block130_eq]
  exact BlockDeterminants.block1_det_isUnit
theorem block130_lower : ∀ (i : Fin 2) (j : Fin 1),
    sourceMatrix (211+1+i.val) (211+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (212+i.val) 211 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column82_lower 1073741824 2 13 11 (-7) i
#print axioms block130_eq
#print axioms block130_unit
#print axioms block130_lower

theorem block131_eq : matrixWindow sourceMatrix 212 1 = BlockDeterminants.block21 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 212 212 = 11
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block51_entry0_0
theorem block131_unit : IsUnit (matrixWindow sourceMatrix 212 1).det := by
  rw [block131_eq]
  exact BlockDeterminants.block21_det_isUnit
theorem block131_lower : ∀ (i : Fin 1) (j : Fin 1),
    sourceMatrix (212+1+i.val) (212+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (213+i.val) 212 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column83_lower 1073741824 2 13 11 (-7) i
#print axioms block131_eq
#print axioms block131_unit
#print axioms block131_lower

theorem block132_eq : matrixWindow sourceMatrix 213 1 = BlockDeterminants.block21 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 213 213 = 11
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block55_entry0_0
theorem block132_unit : IsUnit (matrixWindow sourceMatrix 213 1).det := by
  rw [block132_eq]
  exact BlockDeterminants.block21_det_isUnit
theorem block132_lower : ∀ (i : Fin 0) (j : Fin 1),
    sourceMatrix (213+1+i.val) (213+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (214+i.val) 213 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column88_lower 1073741824 2 13 11 (-7) i
#print axioms block132_eq
#print axioms block132_unit
#print axioms block132_lower

end AspisV8R17.SourceMinor.Windows
