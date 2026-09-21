import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks08
import AspisV8R17.SourceDiagonalBlocks09
import AspisV8R17.SourceLowerBlocks10
import AspisV8R17.SourceLowerBlocks11
import AspisV8R17.SourceLowerBlocks12
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block56_eq : matrixWindow sourceMatrix 83 2 = BlockDeterminants.block6 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 83 83 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block106_entry0_0
    ·
      change sourceMatrix 83 84 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block106_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 84 83 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block106_entry1_0
    ·
      change sourceMatrix 84 84 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block106_entry1_1
theorem block56_unit : IsUnit (matrixWindow sourceMatrix 83 2).det := by
  rw [block56_eq]
  exact BlockDeterminants.block6_det_isUnit
theorem block56_lower : ∀ (i : Fin 129) (j : Fin 2),
    sourceMatrix (83+2+i.val) (83+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (85+i.val) 83 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column163_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (85+i.val) 84 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column164_lower 1073741824 2 13 11 (-7) i
#print axioms block56_eq
#print axioms block56_unit
#print axioms block56_lower

theorem block57_eq : matrixWindow sourceMatrix 85 1 = BlockDeterminants.block19 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 85 85 = 234881024
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block102_entry0_0
theorem block57_unit : IsUnit (matrixWindow sourceMatrix 85 1).det := by
  rw [block57_eq]
  exact BlockDeterminants.block19_det_isUnit
theorem block57_lower : ∀ (i : Fin 128) (j : Fin 1),
    sourceMatrix (85+1+i.val) (85+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (86+i.val) 85 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column157_lower 1073741824 2 13 11 (-7) i
#print axioms block57_eq
#print axioms block57_unit
#print axioms block57_lower

theorem block58_eq : matrixWindow sourceMatrix 86 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 86 86 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block107_entry0_0
    ·
      change sourceMatrix 86 87 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block107_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 87 86 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block107_entry1_0
    ·
      change sourceMatrix 87 87 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block107_entry1_1
theorem block58_unit : IsUnit (matrixWindow sourceMatrix 86 2).det := by
  rw [block58_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block58_lower : ∀ (i : Fin 126) (j : Fin 2),
    sourceMatrix (86+2+i.val) (86+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (88+i.val) 86 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column165_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (88+i.val) 87 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column166_lower 1073741824 2 13 11 (-7) i
#print axioms block58_eq
#print axioms block58_unit
#print axioms block58_lower

theorem block59_eq : matrixWindow sourceMatrix 88 2 = BlockDeterminants.block26 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 88 88 = 939524096
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block108_entry0_0
    ·
      change sourceMatrix 88 89 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block108_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 89 88 = 1476395008
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block108_entry1_0
    ·
      change sourceMatrix 89 89 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block108_entry1_1
theorem block59_unit : IsUnit (matrixWindow sourceMatrix 88 2).det := by
  rw [block59_eq]
  exact BlockDeterminants.block26_det_isUnit
theorem block59_lower : ∀ (i : Fin 124) (j : Fin 2),
    sourceMatrix (88+2+i.val) (88+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (90+i.val) 88 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column167_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (90+i.val) 89 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column168_lower 1073741824 2 13 11 (-7) i
#print axioms block59_eq
#print axioms block59_unit
#print axioms block59_lower

theorem block60_eq : matrixWindow sourceMatrix 90 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 90 90 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block109_entry0_0
    ·
      change sourceMatrix 90 91 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block109_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 91 90 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block109_entry1_0
    ·
      change sourceMatrix 91 91 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block109_entry1_1
theorem block60_unit : IsUnit (matrixWindow sourceMatrix 90 2).det := by
  rw [block60_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block60_lower : ∀ (i : Fin 122) (j : Fin 2),
    sourceMatrix (90+2+i.val) (90+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (92+i.val) 90 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column169_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (92+i.val) 91 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column170_lower 1073741824 2 13 11 (-7) i
#print axioms block60_eq
#print axioms block60_unit
#print axioms block60_lower

theorem block61_eq : matrixWindow sourceMatrix 92 2 = BlockDeterminants.block6 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 92 92 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block110_entry0_0
    ·
      change sourceMatrix 92 93 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block110_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 93 92 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block110_entry1_0
    ·
      change sourceMatrix 93 93 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block110_entry1_1
theorem block61_unit : IsUnit (matrixWindow sourceMatrix 92 2).det := by
  rw [block61_eq]
  exact BlockDeterminants.block6_det_isUnit
theorem block61_lower : ∀ (i : Fin 120) (j : Fin 2),
    sourceMatrix (92+2+i.val) (92+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (94+i.val) 92 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column171_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (94+i.val) 93 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column172_lower 1073741824 2 13 11 (-7) i
#print axioms block61_eq
#print axioms block61_unit
#print axioms block61_lower

theorem block62_eq : matrixWindow sourceMatrix 94 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 94 94 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block111_entry0_0
    ·
      change sourceMatrix 94 95 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block111_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 95 94 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block111_entry1_0
    ·
      change sourceMatrix 95 95 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block111_entry1_1
theorem block62_unit : IsUnit (matrixWindow sourceMatrix 94 2).det := by
  rw [block62_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block62_lower : ∀ (i : Fin 118) (j : Fin 2),
    sourceMatrix (94+2+i.val) (94+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (96+i.val) 94 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column173_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (96+i.val) 95 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column174_lower 1073741824 2 13 11 (-7) i
#print axioms block62_eq
#print axioms block62_unit
#print axioms block62_lower

theorem block63_eq : matrixWindow sourceMatrix 96 2 = BlockDeterminants.block22 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 96 96 = 1879048192
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block112_entry0_0
    ·
      change sourceMatrix 96 97 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block112_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 97 96 = 805306369
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block112_entry1_0
    ·
      change sourceMatrix 97 97 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block112_entry1_1
theorem block63_unit : IsUnit (matrixWindow sourceMatrix 96 2).det := by
  rw [block63_eq]
  exact BlockDeterminants.block22_det_isUnit
theorem block63_lower : ∀ (i : Fin 116) (j : Fin 2),
    sourceMatrix (96+2+i.val) (96+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (98+i.val) 96 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column175_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (98+i.val) 97 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column176_lower 1073741824 2 13 11 (-7) i
#print axioms block63_eq
#print axioms block63_unit
#print axioms block63_lower

end AspisV8R17.SourceMinor.Windows
