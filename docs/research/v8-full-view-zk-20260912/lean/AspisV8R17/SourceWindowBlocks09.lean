import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks01
import AspisV8R17.SourceDiagonalBlocks10
import AspisV8R17.SourceDiagonalBlocks11
import AspisV8R17.SourceLowerBlocks14
import AspisV8R17.SourceLowerBlocks15
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block72_eq : matrixWindow sourceMatrix 114 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 114 114 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block121_entry0_0
    ·
      change sourceMatrix 114 115 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block121_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 115 114 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block121_entry1_0
    ·
      change sourceMatrix 115 115 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block121_entry1_1
theorem block72_unit : IsUnit (matrixWindow sourceMatrix 114 2).det := by
  rw [block72_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block72_lower : ∀ (i : Fin 98) (j : Fin 2),
    sourceMatrix (114+2+i.val) (114+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (116+i.val) 114 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column193_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (116+i.val) 115 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column194_lower 1073741824 2 13 11 (-7) i
#print axioms block72_eq
#print axioms block72_unit
#print axioms block72_lower

theorem block73_eq : matrixWindow sourceMatrix 116 2 = BlockDeterminants.block6 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 116 116 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block122_entry0_0
    ·
      change sourceMatrix 116 117 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block122_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 117 116 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block122_entry1_0
    ·
      change sourceMatrix 117 117 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block122_entry1_1
theorem block73_unit : IsUnit (matrixWindow sourceMatrix 116 2).det := by
  rw [block73_eq]
  exact BlockDeterminants.block6_det_isUnit
theorem block73_lower : ∀ (i : Fin 96) (j : Fin 2),
    sourceMatrix (116+2+i.val) (116+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (118+i.val) 116 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column195_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (118+i.val) 117 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column196_lower 1073741824 2 13 11 (-7) i
#print axioms block73_eq
#print axioms block73_unit
#print axioms block73_lower

theorem block74_eq : matrixWindow sourceMatrix 118 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 118 118 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block123_entry0_0
    ·
      change sourceMatrix 118 119 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block123_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 119 118 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block123_entry1_0
    ·
      change sourceMatrix 119 119 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block123_entry1_1
theorem block74_unit : IsUnit (matrixWindow sourceMatrix 118 2).det := by
  rw [block74_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block74_lower : ∀ (i : Fin 94) (j : Fin 2),
    sourceMatrix (118+2+i.val) (118+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (120+i.val) 118 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column197_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (120+i.val) 119 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column198_lower 1073741824 2 13 11 (-7) i
#print axioms block74_eq
#print axioms block74_unit
#print axioms block74_lower

theorem block75_eq : matrixWindow sourceMatrix 120 2 = BlockDeterminants.block26 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 120 120 = 939524096
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block124_entry0_0
    ·
      change sourceMatrix 120 121 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block124_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 121 120 = 1476395008
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block124_entry1_0
    ·
      change sourceMatrix 121 121 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block124_entry1_1
theorem block75_unit : IsUnit (matrixWindow sourceMatrix 120 2).det := by
  rw [block75_eq]
  exact BlockDeterminants.block26_det_isUnit
theorem block75_lower : ∀ (i : Fin 92) (j : Fin 2),
    sourceMatrix (120+2+i.val) (120+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (122+i.val) 120 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column199_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (122+i.val) 121 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column200_lower 1073741824 2 13 11 (-7) i
#print axioms block75_eq
#print axioms block75_unit
#print axioms block75_lower

theorem block76_eq : matrixWindow sourceMatrix 122 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 122 122 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block10_entry0_0
theorem block76_unit : IsUnit (matrixWindow sourceMatrix 122 1).det := by
  rw [block76_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block76_lower : ∀ (i : Fin 91) (j : Fin 1),
    sourceMatrix (122+1+i.val) (122+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (123+i.val) 122 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column17_lower 1073741824 2 13 11 (-7) i
#print axioms block76_eq
#print axioms block76_unit
#print axioms block76_lower

theorem block77_eq : matrixWindow sourceMatrix 123 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 123 123 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block125_entry0_0
    ·
      change sourceMatrix 123 124 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block125_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 124 123 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block125_entry1_0
    ·
      change sourceMatrix 124 124 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block125_entry1_1
theorem block77_unit : IsUnit (matrixWindow sourceMatrix 123 2).det := by
  rw [block77_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block77_lower : ∀ (i : Fin 89) (j : Fin 2),
    sourceMatrix (123+2+i.val) (123+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (125+i.val) 123 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column201_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (125+i.val) 124 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column202_lower 1073741824 2 13 11 (-7) i
#print axioms block77_eq
#print axioms block77_unit
#print axioms block77_lower

theorem block78_eq : matrixWindow sourceMatrix 125 2 = BlockDeterminants.block6 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 125 125 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block126_entry0_0
    ·
      change sourceMatrix 125 126 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block126_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 126 125 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block126_entry1_0
    ·
      change sourceMatrix 126 126 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block126_entry1_1
theorem block78_unit : IsUnit (matrixWindow sourceMatrix 125 2).det := by
  rw [block78_eq]
  exact BlockDeterminants.block6_det_isUnit
theorem block78_lower : ∀ (i : Fin 87) (j : Fin 2),
    sourceMatrix (125+2+i.val) (125+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (127+i.val) 125 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column203_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (127+i.val) 126 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column204_lower 1073741824 2 13 11 (-7) i
#print axioms block78_eq
#print axioms block78_unit
#print axioms block78_lower

theorem block79_eq : matrixWindow sourceMatrix 127 1 = BlockDeterminants.block10 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 127 127 = 738197504
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block13_entry0_0
theorem block79_unit : IsUnit (matrixWindow sourceMatrix 127 1).det := by
  rw [block79_eq]
  exact BlockDeterminants.block10_det_isUnit
theorem block79_lower : ∀ (i : Fin 86) (j : Fin 1),
    sourceMatrix (127+1+i.val) (127+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (128+i.val) 127 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column22_lower 1073741824 2 13 11 (-7) i
#print axioms block79_eq
#print axioms block79_unit
#print axioms block79_lower

end AspisV8R17.SourceMinor.Windows
