import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks06
import AspisV8R17.SourceDiagonalBlocks07
import AspisV8R17.SourceLowerBlocks04
import AspisV8R17.SourceLowerBlocks05
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block24_eq : matrixWindow sourceMatrix 36 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 36 36 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block72_entry0_0
theorem block24_unit : IsUnit (matrixWindow sourceMatrix 36 1).det := by
  rw [block24_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block24_lower : ∀ (i : Fin 177) (j : Fin 1),
    sourceMatrix (36+1+i.val) (36+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (37+i.val) 36 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column113_lower 1073741824 2 13 11 (-7) i
#print axioms block24_eq
#print axioms block24_unit
#print axioms block24_lower

theorem block25_eq : matrixWindow sourceMatrix 37 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 37 37 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block75_entry0_0
    ·
      change sourceMatrix 37 38 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block75_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 38 37 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block75_entry1_0
    ·
      change sourceMatrix 38 38 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block75_entry1_1
theorem block25_unit : IsUnit (matrixWindow sourceMatrix 37 2).det := by
  rw [block25_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block25_lower : ∀ (i : Fin 175) (j : Fin 2),
    sourceMatrix (37+2+i.val) (37+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (39+i.val) 37 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column117_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (39+i.val) 38 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column118_lower 1073741824 2 13 11 (-7) i
#print axioms block25_eq
#print axioms block25_unit
#print axioms block25_lower

theorem block26_eq : matrixWindow sourceMatrix 39 1 = BlockDeterminants.block24 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 39 39 = 939524096
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block74_entry0_0
theorem block26_unit : IsUnit (matrixWindow sourceMatrix 39 1).det := by
  rw [block26_eq]
  exact BlockDeterminants.block24_det_isUnit
theorem block26_lower : ∀ (i : Fin 174) (j : Fin 1),
    sourceMatrix (39+1+i.val) (39+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (40+i.val) 39 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column116_lower 1073741824 2 13 11 (-7) i
#print axioms block26_eq
#print axioms block26_unit
#print axioms block26_lower

theorem block27_eq : matrixWindow sourceMatrix 40 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 40 40 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block77_entry0_0
    ·
      change sourceMatrix 40 41 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block77_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 41 40 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block77_entry1_0
    ·
      change sourceMatrix 41 41 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block77_entry1_1
theorem block27_unit : IsUnit (matrixWindow sourceMatrix 40 2).det := by
  rw [block27_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block27_lower : ∀ (i : Fin 172) (j : Fin 2),
    sourceMatrix (40+2+i.val) (40+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (42+i.val) 40 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column120_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (42+i.val) 41 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column121_lower 1073741824 2 13 11 (-7) i
#print axioms block27_eq
#print axioms block27_unit
#print axioms block27_lower

theorem block28_eq : matrixWindow sourceMatrix 42 1 = BlockDeterminants.block8 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 42 42 = 1879048192
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block76_entry0_0
theorem block28_unit : IsUnit (matrixWindow sourceMatrix 42 1).det := by
  rw [block28_eq]
  exact BlockDeterminants.block8_det_isUnit
theorem block28_lower : ∀ (i : Fin 171) (j : Fin 1),
    sourceMatrix (42+1+i.val) (42+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (43+i.val) 42 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column119_lower 1073741824 2 13 11 (-7) i
#print axioms block28_eq
#print axioms block28_unit
#print axioms block28_lower

theorem block29_eq : matrixWindow sourceMatrix 43 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 43 43 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block79_entry0_0
    ·
      change sourceMatrix 43 44 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block79_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 44 43 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block79_entry1_0
    ·
      change sourceMatrix 44 44 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block79_entry1_1
theorem block29_unit : IsUnit (matrixWindow sourceMatrix 43 2).det := by
  rw [block29_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block29_lower : ∀ (i : Fin 169) (j : Fin 2),
    sourceMatrix (43+2+i.val) (43+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (45+i.val) 43 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column123_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (45+i.val) 44 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column124_lower 1073741824 2 13 11 (-7) i
#print axioms block29_eq
#print axioms block29_unit
#print axioms block29_lower

theorem block30_eq : matrixWindow sourceMatrix 45 1 = BlockDeterminants.block25 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 45 45 = 469762048
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block78_entry0_0
theorem block30_unit : IsUnit (matrixWindow sourceMatrix 45 1).det := by
  rw [block30_eq]
  exact BlockDeterminants.block25_det_isUnit
theorem block30_lower : ∀ (i : Fin 168) (j : Fin 1),
    sourceMatrix (45+1+i.val) (45+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (46+i.val) 45 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column122_lower 1073741824 2 13 11 (-7) i
#print axioms block30_eq
#print axioms block30_unit
#print axioms block30_lower

theorem block31_eq : matrixWindow sourceMatrix 46 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 46 46 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block81_entry0_0
    ·
      change sourceMatrix 46 47 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block81_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 47 46 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block81_entry1_0
    ·
      change sourceMatrix 47 47 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block81_entry1_1
theorem block31_unit : IsUnit (matrixWindow sourceMatrix 46 2).det := by
  rw [block31_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block31_lower : ∀ (i : Fin 166) (j : Fin 2),
    sourceMatrix (46+2+i.val) (46+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (48+i.val) 46 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column126_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (48+i.val) 47 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column127_lower 1073741824 2 13 11 (-7) i
#print axioms block31_eq
#print axioms block31_unit
#print axioms block31_lower

end AspisV8R17.SourceMinor.Windows
