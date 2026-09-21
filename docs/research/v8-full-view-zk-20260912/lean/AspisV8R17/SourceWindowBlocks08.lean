import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks09
import AspisV8R17.SourceDiagonalBlocks10
import AspisV8R17.SourceLowerBlocks12
import AspisV8R17.SourceLowerBlocks13
import AspisV8R17.SourceLowerBlocks14
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block64_eq : matrixWindow sourceMatrix 98 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 98 98 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block113_entry0_0
    ·
      change sourceMatrix 98 99 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block113_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 99 98 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block113_entry1_0
    ·
      change sourceMatrix 99 99 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block113_entry1_1
theorem block64_unit : IsUnit (matrixWindow sourceMatrix 98 2).det := by
  rw [block64_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block64_lower : ∀ (i : Fin 114) (j : Fin 2),
    sourceMatrix (98+2+i.val) (98+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (100+i.val) 98 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column177_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (100+i.val) 99 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column178_lower 1073741824 2 13 11 (-7) i
#print axioms block64_eq
#print axioms block64_unit
#print axioms block64_lower

theorem block65_eq : matrixWindow sourceMatrix 100 2 = BlockDeterminants.block6 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 100 100 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block114_entry0_0
    ·
      change sourceMatrix 100 101 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block114_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 101 100 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block114_entry1_0
    ·
      change sourceMatrix 101 101 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block114_entry1_1
theorem block65_unit : IsUnit (matrixWindow sourceMatrix 100 2).det := by
  rw [block65_eq]
  exact BlockDeterminants.block6_det_isUnit
theorem block65_lower : ∀ (i : Fin 112) (j : Fin 2),
    sourceMatrix (100+2+i.val) (100+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (102+i.val) 100 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column179_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (102+i.val) 101 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column180_lower 1073741824 2 13 11 (-7) i
#print axioms block65_eq
#print axioms block65_unit
#print axioms block65_lower

theorem block66_eq : matrixWindow sourceMatrix 102 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 102 102 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block115_entry0_0
    ·
      change sourceMatrix 102 103 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block115_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 103 102 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block115_entry1_0
    ·
      change sourceMatrix 103 103 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block115_entry1_1
theorem block66_unit : IsUnit (matrixWindow sourceMatrix 102 2).det := by
  rw [block66_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block66_lower : ∀ (i : Fin 110) (j : Fin 2),
    sourceMatrix (102+2+i.val) (102+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (104+i.val) 102 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column181_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (104+i.val) 103 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column182_lower 1073741824 2 13 11 (-7) i
#print axioms block66_eq
#print axioms block66_unit
#print axioms block66_lower

theorem block67_eq : matrixWindow sourceMatrix 104 2 = BlockDeterminants.block27 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 104 104 = 469762048
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block116_entry0_0
    ·
      change sourceMatrix 104 105 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block116_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 105 104 = 738197504
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block116_entry1_0
    ·
      change sourceMatrix 105 105 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block116_entry1_1
theorem block67_unit : IsUnit (matrixWindow sourceMatrix 104 2).det := by
  rw [block67_eq]
  exact BlockDeterminants.block27_det_isUnit
theorem block67_lower : ∀ (i : Fin 108) (j : Fin 2),
    sourceMatrix (104+2+i.val) (104+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (106+i.val) 104 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column183_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (106+i.val) 105 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column184_lower 1073741824 2 13 11 (-7) i
#print axioms block67_eq
#print axioms block67_unit
#print axioms block67_lower

theorem block68_eq : matrixWindow sourceMatrix 106 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 106 106 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block117_entry0_0
    ·
      change sourceMatrix 106 107 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block117_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 107 106 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block117_entry1_0
    ·
      change sourceMatrix 107 107 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block117_entry1_1
theorem block68_unit : IsUnit (matrixWindow sourceMatrix 106 2).det := by
  rw [block68_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block68_lower : ∀ (i : Fin 106) (j : Fin 2),
    sourceMatrix (106+2+i.val) (106+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (108+i.val) 106 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column185_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (108+i.val) 107 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column186_lower 1073741824 2 13 11 (-7) i
#print axioms block68_eq
#print axioms block68_unit
#print axioms block68_lower

theorem block69_eq : matrixWindow sourceMatrix 108 2 = BlockDeterminants.block6 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 108 108 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block118_entry0_0
    ·
      change sourceMatrix 108 109 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block118_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 109 108 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block118_entry1_0
    ·
      change sourceMatrix 109 109 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block118_entry1_1
theorem block69_unit : IsUnit (matrixWindow sourceMatrix 108 2).det := by
  rw [block69_eq]
  exact BlockDeterminants.block6_det_isUnit
theorem block69_lower : ∀ (i : Fin 104) (j : Fin 2),
    sourceMatrix (108+2+i.val) (108+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (110+i.val) 108 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column187_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (110+i.val) 109 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column188_lower 1073741824 2 13 11 (-7) i
#print axioms block69_eq
#print axioms block69_unit
#print axioms block69_lower

theorem block70_eq : matrixWindow sourceMatrix 110 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 110 110 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block119_entry0_0
    ·
      change sourceMatrix 110 111 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block119_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 111 110 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block119_entry1_0
    ·
      change sourceMatrix 111 111 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block119_entry1_1
theorem block70_unit : IsUnit (matrixWindow sourceMatrix 110 2).det := by
  rw [block70_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block70_lower : ∀ (i : Fin 102) (j : Fin 2),
    sourceMatrix (110+2+i.val) (110+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (112+i.val) 110 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column189_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (112+i.val) 111 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column190_lower 1073741824 2 13 11 (-7) i
#print axioms block70_eq
#print axioms block70_unit
#print axioms block70_lower

theorem block71_eq : matrixWindow sourceMatrix 112 2 = BlockDeterminants.block22 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 112 112 = 1879048192
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block120_entry0_0
    ·
      change sourceMatrix 112 113 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block120_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 113 112 = 805306369
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block120_entry1_0
    ·
      change sourceMatrix 113 113 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block120_entry1_1
theorem block71_unit : IsUnit (matrixWindow sourceMatrix 112 2).det := by
  rw [block71_eq]
  exact BlockDeterminants.block22_det_isUnit
theorem block71_lower : ∀ (i : Fin 100) (j : Fin 2),
    sourceMatrix (112+2+i.val) (112+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (114+i.val) 112 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column191_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (114+i.val) 113 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column192_lower 1073741824 2 13 11 (-7) i
#print axioms block71_eq
#print axioms block71_unit
#print axioms block71_lower

end AspisV8R17.SourceMinor.Windows
