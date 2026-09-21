import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks05
import AspisV8R17.SourceDiagonalBlocks06
import AspisV8R17.SourceLowerBlocks03
import AspisV8R17.SourceLowerBlocks04
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block16_eq : matrixWindow sourceMatrix 24 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 24 24 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block64_entry0_0
theorem block16_unit : IsUnit (matrixWindow sourceMatrix 24 1).det := by
  rw [block16_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block16_lower : ∀ (i : Fin 189) (j : Fin 1),
    sourceMatrix (24+1+i.val) (24+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (25+i.val) 24 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column101_lower 1073741824 2 13 11 (-7) i
#print axioms block16_eq
#print axioms block16_unit
#print axioms block16_lower

theorem block17_eq : matrixWindow sourceMatrix 25 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 25 25 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block67_entry0_0
    ·
      change sourceMatrix 25 26 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block67_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 26 25 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block67_entry1_0
    ·
      change sourceMatrix 26 26 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block67_entry1_1
theorem block17_unit : IsUnit (matrixWindow sourceMatrix 25 2).det := by
  rw [block17_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block17_lower : ∀ (i : Fin 187) (j : Fin 2),
    sourceMatrix (25+2+i.val) (25+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (27+i.val) 25 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column105_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (27+i.val) 26 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column106_lower 1073741824 2 13 11 (-7) i
#print axioms block17_eq
#print axioms block17_unit
#print axioms block17_lower

theorem block18_eq : matrixWindow sourceMatrix 27 1 = BlockDeterminants.block24 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 27 27 = 939524096
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block66_entry0_0
theorem block18_unit : IsUnit (matrixWindow sourceMatrix 27 1).det := by
  rw [block18_eq]
  exact BlockDeterminants.block24_det_isUnit
theorem block18_lower : ∀ (i : Fin 186) (j : Fin 1),
    sourceMatrix (27+1+i.val) (27+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (28+i.val) 27 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column104_lower 1073741824 2 13 11 (-7) i
#print axioms block18_eq
#print axioms block18_unit
#print axioms block18_lower

theorem block19_eq : matrixWindow sourceMatrix 28 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 28 28 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block69_entry0_0
    ·
      change sourceMatrix 28 29 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block69_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 29 28 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block69_entry1_0
    ·
      change sourceMatrix 29 29 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block69_entry1_1
theorem block19_unit : IsUnit (matrixWindow sourceMatrix 28 2).det := by
  rw [block19_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block19_lower : ∀ (i : Fin 184) (j : Fin 2),
    sourceMatrix (28+2+i.val) (28+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (30+i.val) 28 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column108_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (30+i.val) 29 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column109_lower 1073741824 2 13 11 (-7) i
#print axioms block19_eq
#print axioms block19_unit
#print axioms block19_lower

theorem block20_eq : matrixWindow sourceMatrix 30 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 30 30 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block68_entry0_0
theorem block20_unit : IsUnit (matrixWindow sourceMatrix 30 1).det := by
  rw [block20_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block20_lower : ∀ (i : Fin 183) (j : Fin 1),
    sourceMatrix (30+1+i.val) (30+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (31+i.val) 30 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column107_lower 1073741824 2 13 11 (-7) i
#print axioms block20_eq
#print axioms block20_unit
#print axioms block20_lower

theorem block21_eq : matrixWindow sourceMatrix 31 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 31 31 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block71_entry0_0
    ·
      change sourceMatrix 31 32 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block71_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 32 31 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block71_entry1_0
    ·
      change sourceMatrix 32 32 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block71_entry1_1
theorem block21_unit : IsUnit (matrixWindow sourceMatrix 31 2).det := by
  rw [block21_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block21_lower : ∀ (i : Fin 181) (j : Fin 2),
    sourceMatrix (31+2+i.val) (31+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (33+i.val) 31 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column111_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (33+i.val) 32 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column112_lower 1073741824 2 13 11 (-7) i
#print axioms block21_eq
#print axioms block21_unit
#print axioms block21_lower

theorem block22_eq : matrixWindow sourceMatrix 33 1 = BlockDeterminants.block19 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 33 33 = 234881024
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block70_entry0_0
theorem block22_unit : IsUnit (matrixWindow sourceMatrix 33 1).det := by
  rw [block22_eq]
  exact BlockDeterminants.block19_det_isUnit
theorem block22_lower : ∀ (i : Fin 180) (j : Fin 1),
    sourceMatrix (33+1+i.val) (33+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (34+i.val) 33 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column110_lower 1073741824 2 13 11 (-7) i
#print axioms block22_eq
#print axioms block22_unit
#print axioms block22_lower

theorem block23_eq : matrixWindow sourceMatrix 34 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 34 34 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block73_entry0_0
    ·
      change sourceMatrix 34 35 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block73_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 35 34 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block73_entry1_0
    ·
      change sourceMatrix 35 35 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block73_entry1_1
theorem block23_unit : IsUnit (matrixWindow sourceMatrix 34 2).det := by
  rw [block23_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block23_lower : ∀ (i : Fin 178) (j : Fin 2),
    sourceMatrix (34+2+i.val) (34+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (36+i.val) 34 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column114_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (36+i.val) 35 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column115_lower 1073741824 2 13 11 (-7) i
#print axioms block23_eq
#print axioms block23_unit
#print axioms block23_lower

end AspisV8R17.SourceMinor.Windows
