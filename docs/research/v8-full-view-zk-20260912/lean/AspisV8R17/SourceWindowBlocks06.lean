import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks08
import AspisV8R17.SourceDiagonalBlocks09
import AspisV8R17.SourceLowerBlocks09
import AspisV8R17.SourceLowerBlocks10
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block48_eq : matrixWindow sourceMatrix 72 1 = BlockDeterminants.block25 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 72 72 = 469762048
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block94_entry0_0
theorem block48_unit : IsUnit (matrixWindow sourceMatrix 72 1).det := by
  rw [block48_eq]
  exact BlockDeterminants.block25_det_isUnit
theorem block48_lower : ∀ (i : Fin 141) (j : Fin 1),
    sourceMatrix (72+1+i.val) (72+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (73+i.val) 72 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column146_lower 1073741824 2 13 11 (-7) i
#print axioms block48_eq
#print axioms block48_unit
#print axioms block48_lower

theorem block49_eq : matrixWindow sourceMatrix 73 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 73 73 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block96_entry0_0
theorem block49_unit : IsUnit (matrixWindow sourceMatrix 73 1).det := by
  rw [block49_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block49_lower : ∀ (i : Fin 140) (j : Fin 1),
    sourceMatrix (73+1+i.val) (73+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (74+i.val) 73 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column149_lower 1073741824 2 13 11 (-7) i
#print axioms block49_eq
#print axioms block49_unit
#print axioms block49_lower

theorem block50_eq : matrixWindow sourceMatrix 74 1 = BlockDeterminants.block0 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 74 74 = 1073741827
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block97_entry0_0
theorem block50_unit : IsUnit (matrixWindow sourceMatrix 74 1).det := by
  rw [block50_eq]
  exact BlockDeterminants.block0_det_isUnit
theorem block50_lower : ∀ (i : Fin 139) (j : Fin 1),
    sourceMatrix (74+1+i.val) (74+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (75+i.val) 74 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column150_lower 1073741824 2 13 11 (-7) i
#print axioms block50_eq
#print axioms block50_unit
#print axioms block50_lower

theorem block51_eq : matrixWindow sourceMatrix 75 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 75 75 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block99_entry0_0
    ·
      change sourceMatrix 75 76 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block99_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 76 75 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block99_entry1_0
    ·
      change sourceMatrix 76 76 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block99_entry1_1
theorem block51_unit : IsUnit (matrixWindow sourceMatrix 75 2).det := by
  rw [block51_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block51_lower : ∀ (i : Fin 137) (j : Fin 2),
    sourceMatrix (75+2+i.val) (75+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (77+i.val) 75 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column152_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (77+i.val) 76 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column153_lower 1073741824 2 13 11 (-7) i
#print axioms block51_eq
#print axioms block51_unit
#print axioms block51_lower

theorem block52_eq : matrixWindow sourceMatrix 77 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 77 77 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block105_entry0_0
    ·
      change sourceMatrix 77 78 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block105_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 78 77 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block105_entry1_0
    ·
      change sourceMatrix 78 78 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block105_entry1_1
theorem block52_unit : IsUnit (matrixWindow sourceMatrix 77 2).det := by
  rw [block52_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block52_lower : ∀ (i : Fin 135) (j : Fin 2),
    sourceMatrix (77+2+i.val) (77+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (79+i.val) 77 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column161_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (79+i.val) 78 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column162_lower 1073741824 2 13 11 (-7) i
#print axioms block52_eq
#print axioms block52_unit
#print axioms block52_lower

theorem block53_eq : matrixWindow sourceMatrix 79 1 = BlockDeterminants.block24 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 79 79 = 939524096
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block98_entry0_0
theorem block53_unit : IsUnit (matrixWindow sourceMatrix 79 1).det := by
  rw [block53_eq]
  exact BlockDeterminants.block24_det_isUnit
theorem block53_lower : ∀ (i : Fin 134) (j : Fin 1),
    sourceMatrix (79+1+i.val) (79+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (80+i.val) 79 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column151_lower 1073741824 2 13 11 (-7) i
#print axioms block53_eq
#print axioms block53_unit
#print axioms block53_lower

theorem block54_eq : matrixWindow sourceMatrix 80 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 80 80 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block101_entry0_0
    ·
      change sourceMatrix 80 81 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block101_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 81 80 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block101_entry1_0
    ·
      change sourceMatrix 81 81 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block101_entry1_1
theorem block54_unit : IsUnit (matrixWindow sourceMatrix 80 2).det := by
  rw [block54_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block54_lower : ∀ (i : Fin 132) (j : Fin 2),
    sourceMatrix (80+2+i.val) (80+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (82+i.val) 80 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column155_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (82+i.val) 81 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column156_lower 1073741824 2 13 11 (-7) i
#print axioms block54_eq
#print axioms block54_unit
#print axioms block54_lower

theorem block55_eq : matrixWindow sourceMatrix 82 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 82 82 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block100_entry0_0
theorem block55_unit : IsUnit (matrixWindow sourceMatrix 82 1).det := by
  rw [block55_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block55_lower : ∀ (i : Fin 131) (j : Fin 1),
    sourceMatrix (82+1+i.val) (82+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (83+i.val) 82 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column154_lower 1073741824 2 13 11 (-7) i
#print axioms block55_eq
#print axioms block55_unit
#print axioms block55_lower

end AspisV8R17.SourceMinor.Windows
