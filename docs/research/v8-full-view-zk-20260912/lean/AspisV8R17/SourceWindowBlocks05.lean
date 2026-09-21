import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks07
import AspisV8R17.SourceDiagonalBlocks08
import AspisV8R17.SourceLowerBlocks07
import AspisV8R17.SourceLowerBlocks08
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block40_eq : matrixWindow sourceMatrix 60 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 60 60 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block88_entry0_0
theorem block40_unit : IsUnit (matrixWindow sourceMatrix 60 1).det := by
  rw [block40_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block40_lower : ∀ (i : Fin 153) (j : Fin 1),
    sourceMatrix (60+1+i.val) (60+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (61+i.val) 60 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column137_lower 1073741824 2 13 11 (-7) i
#print axioms block40_eq
#print axioms block40_unit
#print axioms block40_lower

theorem block41_eq : matrixWindow sourceMatrix 61 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 61 61 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block91_entry0_0
    ·
      change sourceMatrix 61 62 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block91_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 62 61 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block91_entry1_0
    ·
      change sourceMatrix 62 62 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block91_entry1_1
theorem block41_unit : IsUnit (matrixWindow sourceMatrix 61 2).det := by
  rw [block41_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block41_lower : ∀ (i : Fin 151) (j : Fin 2),
    sourceMatrix (61+2+i.val) (61+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (63+i.val) 61 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column141_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (63+i.val) 62 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column142_lower 1073741824 2 13 11 (-7) i
#print axioms block41_eq
#print axioms block41_unit
#print axioms block41_lower

theorem block42_eq : matrixWindow sourceMatrix 63 1 = BlockDeterminants.block24 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 63 63 = 939524096
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block90_entry0_0
theorem block42_unit : IsUnit (matrixWindow sourceMatrix 63 1).det := by
  rw [block42_eq]
  exact BlockDeterminants.block24_det_isUnit
theorem block42_lower : ∀ (i : Fin 150) (j : Fin 1),
    sourceMatrix (63+1+i.val) (63+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (64+i.val) 63 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column140_lower 1073741824 2 13 11 (-7) i
#print axioms block42_eq
#print axioms block42_unit
#print axioms block42_lower

theorem block43_eq : matrixWindow sourceMatrix 64 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 64 64 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block93_entry0_0
    ·
      change sourceMatrix 64 65 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block93_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 65 64 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block93_entry1_0
    ·
      change sourceMatrix 65 65 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block93_entry1_1
theorem block43_unit : IsUnit (matrixWindow sourceMatrix 64 2).det := by
  rw [block43_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block43_lower : ∀ (i : Fin 148) (j : Fin 2),
    sourceMatrix (64+2+i.val) (64+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (66+i.val) 64 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column144_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (66+i.val) 65 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column145_lower 1073741824 2 13 11 (-7) i
#print axioms block43_eq
#print axioms block43_unit
#print axioms block43_lower

theorem block44_eq : matrixWindow sourceMatrix 66 1 = BlockDeterminants.block0 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 66 66 = 1073741827
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block103_entry0_0
theorem block44_unit : IsUnit (matrixWindow sourceMatrix 66 1).det := by
  rw [block44_eq]
  exact BlockDeterminants.block0_det_isUnit
theorem block44_lower : ∀ (i : Fin 147) (j : Fin 1),
    sourceMatrix (66+1+i.val) (66+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (67+i.val) 66 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column158_lower 1073741824 2 13 11 (-7) i
#print axioms block44_eq
#print axioms block44_unit
#print axioms block44_lower

theorem block45_eq : matrixWindow sourceMatrix 67 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 67 67 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block92_entry0_0
theorem block45_unit : IsUnit (matrixWindow sourceMatrix 67 1).det := by
  rw [block45_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block45_lower : ∀ (i : Fin 146) (j : Fin 1),
    sourceMatrix (67+1+i.val) (67+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (68+i.val) 67 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column143_lower 1073741824 2 13 11 (-7) i
#print axioms block45_eq
#print axioms block45_unit
#print axioms block45_lower

theorem block46_eq : matrixWindow sourceMatrix 68 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 68 68 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block95_entry0_0
    ·
      change sourceMatrix 68 69 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block95_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 69 68 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block95_entry1_0
    ·
      change sourceMatrix 69 69 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block95_entry1_1
theorem block46_unit : IsUnit (matrixWindow sourceMatrix 68 2).det := by
  rw [block46_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block46_lower : ∀ (i : Fin 144) (j : Fin 2),
    sourceMatrix (68+2+i.val) (68+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (70+i.val) 68 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column147_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (70+i.val) 69 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column148_lower 1073741824 2 13 11 (-7) i
#print axioms block46_eq
#print axioms block46_unit
#print axioms block46_lower

theorem block47_eq : matrixWindow sourceMatrix 70 2 = BlockDeterminants.block22 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 70 70 = 1879048192
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block104_entry0_0
    ·
      change sourceMatrix 70 71 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block104_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 71 70 = 805306369
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block104_entry1_0
    ·
      change sourceMatrix 71 71 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block104_entry1_1
theorem block47_unit : IsUnit (matrixWindow sourceMatrix 70 2).det := by
  rw [block47_eq]
  exact BlockDeterminants.block22_det_isUnit
theorem block47_lower : ∀ (i : Fin 142) (j : Fin 2),
    sourceMatrix (70+2+i.val) (70+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (72+i.val) 70 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column159_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (72+i.val) 71 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column160_lower 1073741824 2 13 11 (-7) i
#print axioms block47_eq
#print axioms block47_unit
#print axioms block47_lower

end AspisV8R17.SourceMinor.Windows
