import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks05
import AspisV8R17.SourceDiagonalBlocks06
import AspisV8R17.SourceLowerBlocks01
import AspisV8R17.SourceLowerBlocks02
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block8_eq : matrixWindow sourceMatrix 12 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 12 12 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block56_entry0_0
theorem block8_unit : IsUnit (matrixWindow sourceMatrix 12 1).det := by
  rw [block8_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block8_lower : ∀ (i : Fin 201) (j : Fin 1),
    sourceMatrix (12+1+i.val) (12+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (13+i.val) 12 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column89_lower 1073741824 2 13 11 (-7) i
#print axioms block8_eq
#print axioms block8_unit
#print axioms block8_lower

theorem block9_eq : matrixWindow sourceMatrix 13 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 13 13 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block59_entry0_0
    ·
      change sourceMatrix 13 14 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block59_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 14 13 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block59_entry1_0
    ·
      change sourceMatrix 14 14 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block59_entry1_1
theorem block9_unit : IsUnit (matrixWindow sourceMatrix 13 2).det := by
  rw [block9_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block9_lower : ∀ (i : Fin 199) (j : Fin 2),
    sourceMatrix (13+2+i.val) (13+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (15+i.val) 13 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column93_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (15+i.val) 14 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column94_lower 1073741824 2 13 11 (-7) i
#print axioms block9_eq
#print axioms block9_unit
#print axioms block9_lower

theorem block10_eq : matrixWindow sourceMatrix 15 1 = BlockDeterminants.block24 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 15 15 = 939524096
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block58_entry0_0
theorem block10_unit : IsUnit (matrixWindow sourceMatrix 15 1).det := by
  rw [block10_eq]
  exact BlockDeterminants.block24_det_isUnit
theorem block10_lower : ∀ (i : Fin 198) (j : Fin 1),
    sourceMatrix (15+1+i.val) (15+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (16+i.val) 15 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column92_lower 1073741824 2 13 11 (-7) i
#print axioms block10_eq
#print axioms block10_unit
#print axioms block10_lower

theorem block11_eq : matrixWindow sourceMatrix 16 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 16 16 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block61_entry0_0
    ·
      change sourceMatrix 16 17 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block61_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 17 16 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block61_entry1_0
    ·
      change sourceMatrix 17 17 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block61_entry1_1
theorem block11_unit : IsUnit (matrixWindow sourceMatrix 16 2).det := by
  rw [block11_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block11_lower : ∀ (i : Fin 196) (j : Fin 2),
    sourceMatrix (16+2+i.val) (16+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (18+i.val) 16 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column96_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (18+i.val) 17 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column97_lower 1073741824 2 13 11 (-7) i
#print axioms block11_eq
#print axioms block11_unit
#print axioms block11_lower

theorem block12_eq : matrixWindow sourceMatrix 18 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 18 18 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block60_entry0_0
theorem block12_unit : IsUnit (matrixWindow sourceMatrix 18 1).det := by
  rw [block12_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block12_lower : ∀ (i : Fin 195) (j : Fin 1),
    sourceMatrix (18+1+i.val) (18+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (19+i.val) 18 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column95_lower 1073741824 2 13 11 (-7) i
#print axioms block12_eq
#print axioms block12_unit
#print axioms block12_lower

theorem block13_eq : matrixWindow sourceMatrix 19 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 19 19 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block63_entry0_0
    ·
      change sourceMatrix 19 20 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block63_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 20 19 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block63_entry1_0
    ·
      change sourceMatrix 20 20 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block63_entry1_1
theorem block13_unit : IsUnit (matrixWindow sourceMatrix 19 2).det := by
  rw [block13_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block13_lower : ∀ (i : Fin 193) (j : Fin 2),
    sourceMatrix (19+2+i.val) (19+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (21+i.val) 19 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column99_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (21+i.val) 20 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column100_lower 1073741824 2 13 11 (-7) i
#print axioms block13_eq
#print axioms block13_unit
#print axioms block13_lower

theorem block14_eq : matrixWindow sourceMatrix 21 1 = BlockDeterminants.block25 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 21 21 = 469762048
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block62_entry0_0
theorem block14_unit : IsUnit (matrixWindow sourceMatrix 21 1).det := by
  rw [block14_eq]
  exact BlockDeterminants.block25_det_isUnit
theorem block14_lower : ∀ (i : Fin 192) (j : Fin 1),
    sourceMatrix (21+1+i.val) (21+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (22+i.val) 21 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column98_lower 1073741824 2 13 11 (-7) i
#print axioms block14_eq
#print axioms block14_unit
#print axioms block14_lower

theorem block15_eq : matrixWindow sourceMatrix 22 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 22 22 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block65_entry0_0
    ·
      change sourceMatrix 22 23 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block65_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 23 22 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block65_entry1_0
    ·
      change sourceMatrix 23 23 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block65_entry1_1
theorem block15_unit : IsUnit (matrixWindow sourceMatrix 22 2).det := by
  rw [block15_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block15_lower : ∀ (i : Fin 190) (j : Fin 2),
    sourceMatrix (22+2+i.val) (22+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (24+i.val) 22 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column102_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (24+i.val) 23 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column103_lower 1073741824 2 13 11 (-7) i
#print axioms block15_eq
#print axioms block15_unit
#print axioms block15_lower

end AspisV8R17.SourceMinor.Windows
