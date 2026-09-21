import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks00
import AspisV8R17.SourceDiagonalBlocks02
import AspisV8R17.SourceDiagonalBlocks03
import AspisV8R17.SourceDiagonalBlocks04
import AspisV8R17.SourceDiagonalBlocks11
import AspisV8R17.SourceDiagonalBlocks12
import AspisV8R17.SourceLowerBlocks16
import AspisV8R17.SourceLowerBlocks17
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block80_eq : matrixWindow sourceMatrix 128 2 = BlockDeterminants.block15 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 128 128 = 117440512
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block22_entry0_0
    ·
      change sourceMatrix 128 129 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block22_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 129 128 = 184549376
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block22_entry1_0
    ·
      change sourceMatrix 129 129 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block22_entry1_1
theorem block80_unit : IsUnit (matrixWindow sourceMatrix 128 2).det := by
  rw [block80_eq]
  exact BlockDeterminants.block15_det_isUnit
theorem block80_lower : ∀ (i : Fin 84) (j : Fin 2),
    sourceMatrix (128+2+i.val) (128+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (130+i.val) 128 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column36_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (130+i.val) 129 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column37_lower 1073741824 2 13 11 (-7) i
#print axioms block80_eq
#print axioms block80_unit
#print axioms block80_lower

theorem block81_eq : matrixWindow sourceMatrix 130 3 = BlockDeterminants.block28 := by
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 130 130 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block127_entry0_0
    ·
      change sourceMatrix 130 131 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block127_entry0_1
    ·
      change sourceMatrix 130 132 = 28
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block127_entry0_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 131 130 = 0
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block127_entry1_0
    ·
      change sourceMatrix 131 131 = 1879048192
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block127_entry1_1
    ·
      change sourceMatrix 131 132 = 805306369
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block127_entry1_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 132 130 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block127_entry2_0
    ·
      change sourceMatrix 132 131 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block127_entry2_1
    ·
      change sourceMatrix 132 132 = 2147483616
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block127_entry2_2
theorem block81_unit : IsUnit (matrixWindow sourceMatrix 130 3).det := by
  rw [block81_eq]
  exact BlockDeterminants.block28_det_isUnit
theorem block81_lower : ∀ (i : Fin 81) (j : Fin 3),
    sourceMatrix (130+3+i.val) (130+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  ·
    change sourceMatrix (133+i.val) 130 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column205_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (133+i.val) 131 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column206_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (133+i.val) 132 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column207_lower 1073741824 2 13 11 (-7) i
#print axioms block81_eq
#print axioms block81_unit
#print axioms block81_lower

theorem block82_eq : matrixWindow sourceMatrix 133 3 = BlockDeterminants.block17 := by
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 133 133 = 738197504
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block30_entry0_0
    ·
      change sourceMatrix 133 134 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block30_entry0_1
    ·
      change sourceMatrix 133 135 = 28
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block30_entry0_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 134 133 = 0
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block30_entry1_0
    ·
      change sourceMatrix 134 134 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block30_entry1_1
    ·
      change sourceMatrix 134 135 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block30_entry1_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 135 133 = 469762048
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block30_entry2_0
    ·
      change sourceMatrix 135 134 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block30_entry2_1
    ·
      change sourceMatrix 135 135 = 2147483616
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block30_entry2_2
theorem block82_unit : IsUnit (matrixWindow sourceMatrix 133 3).det := by
  rw [block82_eq]
  exact BlockDeterminants.block17_det_isUnit
theorem block82_lower : ∀ (i : Fin 78) (j : Fin 3),
    sourceMatrix (133+3+i.val) (133+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  ·
    change sourceMatrix (136+i.val) 133 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column50_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (136+i.val) 134 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column51_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (136+i.val) 135 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column52_lower 1073741824 2 13 11 (-7) i
#print axioms block82_eq
#print axioms block82_unit
#print axioms block82_lower

theorem block83_eq : matrixWindow sourceMatrix 136 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 136 136 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block128_entry0_0
theorem block83_unit : IsUnit (matrixWindow sourceMatrix 136 1).det := by
  rw [block83_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block83_lower : ∀ (i : Fin 77) (j : Fin 1),
    sourceMatrix (136+1+i.val) (136+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (137+i.val) 136 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column208_lower 1073741824 2 13 11 (-7) i
#print axioms block83_eq
#print axioms block83_unit
#print axioms block83_lower

theorem block84_eq : matrixWindow sourceMatrix 137 1 = BlockDeterminants.block19 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 137 137 = 234881024
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block38_entry0_0
theorem block84_unit : IsUnit (matrixWindow sourceMatrix 137 1).det := by
  rw [block84_eq]
  exact BlockDeterminants.block19_det_isUnit
theorem block84_lower : ∀ (i : Fin 76) (j : Fin 1),
    sourceMatrix (137+1+i.val) (137+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (138+i.val) 137 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column65_lower 1073741824 2 13 11 (-7) i
#print axioms block84_eq
#print axioms block84_unit
#print axioms block84_lower

theorem block85_eq : matrixWindow sourceMatrix 138 1 = BlockDeterminants.block0 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 138 138 = 1073741827
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block129_entry0_0
theorem block85_unit : IsUnit (matrixWindow sourceMatrix 138 1).det := by
  rw [block85_eq]
  exact BlockDeterminants.block0_det_isUnit
theorem block85_lower : ∀ (i : Fin 75) (j : Fin 1),
    sourceMatrix (138+1+i.val) (138+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (139+i.val) 138 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column209_lower 1073741824 2 13 11 (-7) i
#print axioms block85_eq
#print axioms block85_unit
#print axioms block85_lower

theorem block86_eq : matrixWindow sourceMatrix 139 1 = BlockDeterminants.block0 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 139 139 = 1073741827
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block130_entry0_0
theorem block86_unit : IsUnit (matrixWindow sourceMatrix 139 1).det := by
  rw [block86_eq]
  exact BlockDeterminants.block0_det_isUnit
theorem block86_lower : ∀ (i : Fin 74) (j : Fin 1),
    sourceMatrix (139+1+i.val) (139+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (140+i.val) 139 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column210_lower 1073741824 2 13 11 (-7) i
#print axioms block86_eq
#print axioms block86_unit
#print axioms block86_lower

theorem block87_eq : matrixWindow sourceMatrix 140 3 = BlockDeterminants.block2 := by
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 140 140 = 805306369
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block2_entry0_0
    ·
      change sourceMatrix 140 141 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block2_entry0_1
    ·
      change sourceMatrix 140 142 = 28
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block2_entry0_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 141 140 = 0
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block2_entry1_0
    ·
      change sourceMatrix 141 141 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block2_entry1_1
    ·
      change sourceMatrix 141 142 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block2_entry1_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 142 140 = 1879048192
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block2_entry2_0
    ·
      change sourceMatrix 142 141 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block2_entry2_1
    ·
      change sourceMatrix 142 142 = 2147483616
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block2_entry2_2
theorem block87_unit : IsUnit (matrixWindow sourceMatrix 140 3).det := by
  rw [block87_eq]
  exact BlockDeterminants.block2_det_isUnit
theorem block87_lower : ∀ (i : Fin 71) (j : Fin 3),
    sourceMatrix (140+3+i.val) (140+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  ·
    change sourceMatrix (143+i.val) 140 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column2_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (143+i.val) 141 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column3_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (143+i.val) 142 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column4_lower 1073741824 2 13 11 (-7) i
#print axioms block87_eq
#print axioms block87_unit
#print axioms block87_lower

end AspisV8R17.SourceMinor.Windows
