import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks00
import AspisV8R17.SourceDiagonalBlocks01
import AspisV8R17.SourceDiagonalBlocks02
import AspisV8R17.SourceLowerBlocks17
import AspisV8R17.SourceLowerBlocks18
import AspisV8R17.SourceLowerBlocks19
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block88_eq : matrixWindow sourceMatrix 143 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 143 143 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block5_entry0_0
    ·
      change sourceMatrix 143 144 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block5_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 144 143 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block5_entry1_0
    ·
      change sourceMatrix 144 144 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block5_entry1_1
theorem block88_unit : IsUnit (matrixWindow sourceMatrix 143 2).det := by
  rw [block88_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block88_lower : ∀ (i : Fin 69) (j : Fin 2),
    sourceMatrix (143+2+i.val) (143+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (145+i.val) 143 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column8_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (145+i.val) 144 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column9_lower 1073741824 2 13 11 (-7) i
#print axioms block88_eq
#print axioms block88_unit
#print axioms block88_lower

theorem block89_eq : matrixWindow sourceMatrix 145 1 = BlockDeterminants.block5 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 145 145 = 1610612737
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block7_entry0_0
theorem block89_unit : IsUnit (matrixWindow sourceMatrix 145 1).det := by
  rw [block89_eq]
  exact BlockDeterminants.block5_det_isUnit
theorem block89_lower : ∀ (i : Fin 68) (j : Fin 1),
    sourceMatrix (145+1+i.val) (145+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (146+i.val) 145 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column11_lower 1073741824 2 13 11 (-7) i
#print axioms block89_eq
#print axioms block89_unit
#print axioms block89_lower

theorem block90_eq : matrixWindow sourceMatrix 146 3 = BlockDeterminants.block7 := by
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 146 146 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block9_entry0_0
    ·
      change sourceMatrix 146 147 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block9_entry0_1
    ·
      change sourceMatrix 146 148 = 28
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block9_entry0_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 147 146 = 0
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block9_entry1_0
    ·
      change sourceMatrix 147 147 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block9_entry1_1
    ·
      change sourceMatrix 147 148 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block9_entry1_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 148 146 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block9_entry2_0
    ·
      change sourceMatrix 148 147 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block9_entry2_1
    ·
      change sourceMatrix 148 148 = 2147483616
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block9_entry2_2
theorem block90_unit : IsUnit (matrixWindow sourceMatrix 146 3).det := by
  rw [block90_eq]
  exact BlockDeterminants.block7_det_isUnit
theorem block90_lower : ∀ (i : Fin 65) (j : Fin 3),
    sourceMatrix (146+3+i.val) (146+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  ·
    change sourceMatrix (149+i.val) 146 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column14_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (149+i.val) 147 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column15_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (149+i.val) 148 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column16_lower 1073741824 2 13 11 (-7) i
#print axioms block90_eq
#print axioms block90_unit
#print axioms block90_lower

theorem block91_eq : matrixWindow sourceMatrix 149 1 = BlockDeterminants.block0 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 149 149 = 1073741827
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block14_entry0_0
theorem block91_unit : IsUnit (matrixWindow sourceMatrix 149 1).det := by
  rw [block91_eq]
  exact BlockDeterminants.block0_det_isUnit
theorem block91_lower : ∀ (i : Fin 64) (j : Fin 1),
    sourceMatrix (149+1+i.val) (149+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (150+i.val) 149 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column23_lower 1073741824 2 13 11 (-7) i
#print axioms block91_eq
#print axioms block91_unit
#print axioms block91_lower

theorem block92_eq : matrixWindow sourceMatrix 150 3 = BlockDeterminants.block12 := by
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 150 150 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block16_entry0_0
    ·
      change sourceMatrix 150 151 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block16_entry0_1
    ·
      change sourceMatrix 150 152 = 28
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block16_entry0_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 151 150 = 0
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block16_entry1_0
    ·
      change sourceMatrix 151 151 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block16_entry1_1
    ·
      change sourceMatrix 151 152 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block16_entry1_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 152 150 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block16_entry2_0
    ·
      change sourceMatrix 152 151 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block16_entry2_1
    ·
      change sourceMatrix 152 152 = 2147483616
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block16_entry2_2
theorem block92_unit : IsUnit (matrixWindow sourceMatrix 150 3).det := by
  rw [block92_eq]
  exact BlockDeterminants.block12_det_isUnit
theorem block92_lower : ∀ (i : Fin 61) (j : Fin 3),
    sourceMatrix (150+3+i.val) (150+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  ·
    change sourceMatrix (153+i.val) 150 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column26_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (153+i.val) 151 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column27_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (153+i.val) 152 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column28_lower 1073741824 2 13 11 (-7) i
#print axioms block92_eq
#print axioms block92_unit
#print axioms block92_lower

theorem block93_eq : matrixWindow sourceMatrix 153 1 = BlockDeterminants.block0 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 153 153 = 1073741827
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block17_entry0_0
theorem block93_unit : IsUnit (matrixWindow sourceMatrix 153 1).det := by
  rw [block93_eq]
  exact BlockDeterminants.block0_det_isUnit
theorem block93_lower : ∀ (i : Fin 60) (j : Fin 1),
    sourceMatrix (153+1+i.val) (153+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (154+i.val) 153 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column29_lower 1073741824 2 13 11 (-7) i
#print axioms block93_eq
#print axioms block93_unit
#print axioms block93_lower

theorem block94_eq : matrixWindow sourceMatrix 154 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 154 154 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block19_entry0_0
    ·
      change sourceMatrix 154 155 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block19_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 155 154 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block19_entry1_0
    ·
      change sourceMatrix 155 155 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block19_entry1_1
theorem block94_unit : IsUnit (matrixWindow sourceMatrix 154 2).det := by
  rw [block94_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block94_lower : ∀ (i : Fin 58) (j : Fin 2),
    sourceMatrix (154+2+i.val) (154+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (156+i.val) 154 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column32_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (156+i.val) 155 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column33_lower 1073741824 2 13 11 (-7) i
#print axioms block94_eq
#print axioms block94_unit
#print axioms block94_lower

theorem block95_eq : matrixWindow sourceMatrix 156 3 = BlockDeterminants.block7 := by
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 156 156 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block23_entry0_0
    ·
      change sourceMatrix 156 157 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block23_entry0_1
    ·
      change sourceMatrix 156 158 = 28
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block23_entry0_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 157 156 = 0
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block23_entry1_0
    ·
      change sourceMatrix 157 157 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block23_entry1_1
    ·
      change sourceMatrix 157 158 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block23_entry1_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 158 156 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block23_entry2_0
    ·
      change sourceMatrix 158 157 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block23_entry2_1
    ·
      change sourceMatrix 158 158 = 2147483616
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block23_entry2_2
theorem block95_unit : IsUnit (matrixWindow sourceMatrix 156 3).det := by
  rw [block95_eq]
  exact BlockDeterminants.block7_det_isUnit
theorem block95_lower : ∀ (i : Fin 55) (j : Fin 3),
    sourceMatrix (156+3+i.val) (156+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  ·
    change sourceMatrix (159+i.val) 156 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column38_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (159+i.val) 157 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column39_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (159+i.val) 158 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column40_lower 1073741824 2 13 11 (-7) i
#print axioms block95_eq
#print axioms block95_unit
#print axioms block95_lower

end AspisV8R17.SourceMinor.Windows
