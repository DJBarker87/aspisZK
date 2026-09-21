import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks00
import AspisV8R17.SourceDiagonalBlocks01
import AspisV8R17.SourceDiagonalBlocks02
import AspisV8R17.SourceDiagonalBlocks04
import AspisV8R17.SourceDiagonalBlocks12
import AspisV8R17.SourceLowerBlocks21
import AspisV8R17.SourceLowerBlocks22
import AspisV8R17.SourceLowerBlocks23
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block104_eq : matrixWindow sourceMatrix 172 3 = BlockDeterminants.block12 := by
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 172 172 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block44_entry0_0
    ·
      change sourceMatrix 172 173 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block44_entry0_1
    ·
      change sourceMatrix 172 174 = 28
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block44_entry0_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 173 172 = 0
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block44_entry1_0
    ·
      change sourceMatrix 173 173 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block44_entry1_1
    ·
      change sourceMatrix 173 174 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block44_entry1_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 174 172 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block44_entry2_0
    ·
      change sourceMatrix 174 173 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block44_entry2_1
    ·
      change sourceMatrix 174 174 = 2147483616
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block44_entry2_2
theorem block104_unit : IsUnit (matrixWindow sourceMatrix 172 3).det := by
  rw [block104_eq]
  exact BlockDeterminants.block12_det_isUnit
theorem block104_lower : ∀ (i : Fin 39) (j : Fin 3),
    sourceMatrix (172+3+i.val) (172+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  ·
    change sourceMatrix (175+i.val) 172 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column73_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (175+i.val) 173 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column74_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (175+i.val) 174 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column75_lower 1073741824 2 13 11 (-7) i
#print axioms block104_eq
#print axioms block104_unit
#print axioms block104_lower

theorem block105_eq : matrixWindow sourceMatrix 175 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 175 175 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block48_entry0_0
theorem block105_unit : IsUnit (matrixWindow sourceMatrix 175 1).det := by
  rw [block105_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block105_lower : ∀ (i : Fin 38) (j : Fin 1),
    sourceMatrix (175+1+i.val) (175+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (176+i.val) 175 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column79_lower 1073741824 2 13 11 (-7) i
#print axioms block105_eq
#print axioms block105_unit
#print axioms block105_lower

theorem block106_eq : matrixWindow sourceMatrix 176 1 = BlockDeterminants.block21 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 176 176 = 11
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block131_entry0_0
theorem block106_unit : IsUnit (matrixWindow sourceMatrix 176 1).det := by
  rw [block106_eq]
  exact BlockDeterminants.block21_det_isUnit
theorem block106_lower : ∀ (i : Fin 37) (j : Fin 1),
    sourceMatrix (176+1+i.val) (176+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (177+i.val) 176 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column211_lower 1073741824 2 13 11 (-7) i
#print axioms block106_eq
#print axioms block106_unit
#print axioms block106_lower

theorem block107_eq : matrixWindow sourceMatrix 177 2 = BlockDeterminants.block6 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 177 177 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block8_entry0_0
    ·
      change sourceMatrix 177 178 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block8_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 178 177 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block8_entry1_0
    ·
      change sourceMatrix 178 178 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block8_entry1_1
theorem block107_unit : IsUnit (matrixWindow sourceMatrix 177 2).det := by
  rw [block107_eq]
  exact BlockDeterminants.block6_det_isUnit
theorem block107_lower : ∀ (i : Fin 35) (j : Fin 2),
    sourceMatrix (177+2+i.val) (177+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (179+i.val) 177 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column12_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (179+i.val) 178 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column13_lower 1073741824 2 13 11 (-7) i
#print axioms block107_eq
#print axioms block107_unit
#print axioms block107_lower

theorem block108_eq : matrixWindow sourceMatrix 179 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 179 179 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block11_entry0_0
    ·
      change sourceMatrix 179 180 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block11_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 180 179 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block11_entry1_0
    ·
      change sourceMatrix 180 180 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block11_entry1_1
theorem block108_unit : IsUnit (matrixWindow sourceMatrix 179 2).det := by
  rw [block108_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block108_lower : ∀ (i : Fin 33) (j : Fin 2),
    sourceMatrix (179+2+i.val) (179+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (181+i.val) 179 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column18_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (181+i.val) 180 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column19_lower 1073741824 2 13 11 (-7) i
#print axioms block108_eq
#print axioms block108_unit
#print axioms block108_lower

theorem block109_eq : matrixWindow sourceMatrix 181 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 181 181 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block15_entry0_0
    ·
      change sourceMatrix 181 182 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block15_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 182 181 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block15_entry1_0
    ·
      change sourceMatrix 182 182 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block15_entry1_1
theorem block109_unit : IsUnit (matrixWindow sourceMatrix 181 2).det := by
  rw [block109_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block109_lower : ∀ (i : Fin 31) (j : Fin 2),
    sourceMatrix (181+2+i.val) (181+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (183+i.val) 181 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column24_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (183+i.val) 182 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column25_lower 1073741824 2 13 11 (-7) i
#print axioms block109_eq
#print axioms block109_unit
#print axioms block109_lower

theorem block110_eq : matrixWindow sourceMatrix 183 2 = BlockDeterminants.block13 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 183 183 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block18_entry0_0
    ·
      change sourceMatrix 183 184 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block18_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 184 183 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block18_entry1_0
    ·
      change sourceMatrix 184 184 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block18_entry1_1
theorem block110_unit : IsUnit (matrixWindow sourceMatrix 183 2).det := by
  rw [block110_eq]
  exact BlockDeterminants.block13_det_isUnit
theorem block110_lower : ∀ (i : Fin 29) (j : Fin 2),
    sourceMatrix (183+2+i.val) (183+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (185+i.val) 183 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column30_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (185+i.val) 184 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column31_lower 1073741824 2 13 11 (-7) i
#print axioms block110_eq
#print axioms block110_unit
#print axioms block110_lower

theorem block111_eq : matrixWindow sourceMatrix 185 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 185 185 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block25_entry0_0
    ·
      change sourceMatrix 185 186 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block25_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 186 185 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block25_entry1_0
    ·
      change sourceMatrix 186 186 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block25_entry1_1
theorem block111_unit : IsUnit (matrixWindow sourceMatrix 185 2).det := by
  rw [block111_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block111_lower : ∀ (i : Fin 27) (j : Fin 2),
    sourceMatrix (185+2+i.val) (185+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (187+i.val) 185 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column42_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (187+i.val) 186 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column43_lower 1073741824 2 13 11 (-7) i
#print axioms block111_eq
#print axioms block111_unit
#print axioms block111_lower

end AspisV8R17.SourceMinor.Windows
