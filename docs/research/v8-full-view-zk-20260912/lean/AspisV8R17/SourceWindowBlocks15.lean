import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks00
import AspisV8R17.SourceDiagonalBlocks02
import AspisV8R17.SourceDiagonalBlocks03
import AspisV8R17.SourceDiagonalBlocks04
import AspisV8R17.SourceLowerBlocks25
import AspisV8R17.SourceLowerBlocks26
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block120_eq : matrixWindow sourceMatrix 201 1 = BlockDeterminants.block1 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 201 201 = 1073741829
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block1_entry0_0
theorem block120_unit : IsUnit (matrixWindow sourceMatrix 201 1).det := by
  rw [block120_eq]
  exact BlockDeterminants.block1_det_isUnit
theorem block120_lower : ∀ (i : Fin 12) (j : Fin 1),
    sourceMatrix (201+1+i.val) (201+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (202+i.val) 201 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column1_lower 1073741824 2 13 11 (-7) i
#print axioms block120_eq
#print axioms block120_unit
#print axioms block120_lower

theorem block121_eq : matrixWindow sourceMatrix 202 1 = BlockDeterminants.block1 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 202 202 = 1073741829
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block6_entry0_0
theorem block121_unit : IsUnit (matrixWindow sourceMatrix 202 1).det := by
  rw [block121_eq]
  exact BlockDeterminants.block1_det_isUnit
theorem block121_lower : ∀ (i : Fin 11) (j : Fin 1),
    sourceMatrix (202+1+i.val) (202+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (203+i.val) 202 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column10_lower 1073741824 2 13 11 (-7) i
#print axioms block121_eq
#print axioms block121_unit
#print axioms block121_lower

theorem block122_eq : matrixWindow sourceMatrix 203 1 = BlockDeterminants.block1 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 203 203 = 1073741829
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block20_entry0_0
theorem block122_unit : IsUnit (matrixWindow sourceMatrix 203 1).det := by
  rw [block122_eq]
  exact BlockDeterminants.block1_det_isUnit
theorem block122_lower : ∀ (i : Fin 10) (j : Fin 1),
    sourceMatrix (203+1+i.val) (203+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (204+i.val) 203 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column34_lower 1073741824 2 13 11 (-7) i
#print axioms block122_eq
#print axioms block122_unit
#print axioms block122_lower

theorem block123_eq : matrixWindow sourceMatrix 204 1 = BlockDeterminants.block16 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 204 204 = 1610612738
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block27_entry0_0
theorem block123_unit : IsUnit (matrixWindow sourceMatrix 204 1).det := by
  rw [block123_eq]
  exact BlockDeterminants.block16_det_isUnit
theorem block123_lower : ∀ (i : Fin 9) (j : Fin 1),
    sourceMatrix (204+1+i.val) (204+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (205+i.val) 204 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column46_lower 1073741824 2 13 11 (-7) i
#print axioms block123_eq
#print axioms block123_unit
#print axioms block123_lower

theorem block124_eq : matrixWindow sourceMatrix 205 1 = BlockDeterminants.block1 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 205 205 = 1073741829
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block34_entry0_0
theorem block124_unit : IsUnit (matrixWindow sourceMatrix 205 1).det := by
  rw [block124_eq]
  exact BlockDeterminants.block1_det_isUnit
theorem block124_lower : ∀ (i : Fin 8) (j : Fin 1),
    sourceMatrix (205+1+i.val) (205+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (206+i.val) 205 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column58_lower 1073741824 2 13 11 (-7) i
#print axioms block124_eq
#print axioms block124_unit
#print axioms block124_lower

theorem block125_eq : matrixWindow sourceMatrix 206 1 = BlockDeterminants.block20 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 206 206 = 805306369
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block41_entry0_0
theorem block125_unit : IsUnit (matrixWindow sourceMatrix 206 1).det := by
  rw [block125_eq]
  exact BlockDeterminants.block20_det_isUnit
theorem block125_lower : ∀ (i : Fin 7) (j : Fin 1),
    sourceMatrix (206+1+i.val) (206+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (207+i.val) 206 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column70_lower 1073741824 2 13 11 (-7) i
#print axioms block125_eq
#print axioms block125_unit
#print axioms block125_lower

theorem block126_eq : matrixWindow sourceMatrix 207 1 = BlockDeterminants.block0 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 207 207 = 1073741827
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block42_entry0_0
theorem block126_unit : IsUnit (matrixWindow sourceMatrix 207 1).det := by
  rw [block126_eq]
  exact BlockDeterminants.block0_det_isUnit
theorem block126_lower : ∀ (i : Fin 6) (j : Fin 1),
    sourceMatrix (207+1+i.val) (207+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (208+i.val) 207 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column71_lower 1073741824 2 13 11 (-7) i
#print axioms block126_eq
#print axioms block126_unit
#print axioms block126_lower

theorem block127_eq : matrixWindow sourceMatrix 208 1 = BlockDeterminants.block1 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 208 208 = 1073741829
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block43_entry0_0
theorem block127_unit : IsUnit (matrixWindow sourceMatrix 208 1).det := by
  rw [block127_eq]
  exact BlockDeterminants.block1_det_isUnit
theorem block127_lower : ∀ (i : Fin 5) (j : Fin 1),
    sourceMatrix (208+1+i.val) (208+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (209+i.val) 208 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column72_lower 1073741824 2 13 11 (-7) i
#print axioms block127_eq
#print axioms block127_unit
#print axioms block127_lower

end AspisV8R17.SourceMinor.Windows
