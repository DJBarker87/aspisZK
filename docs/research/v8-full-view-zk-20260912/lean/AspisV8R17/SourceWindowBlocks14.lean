import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks00
import AspisV8R17.SourceDiagonalBlocks02
import AspisV8R17.SourceDiagonalBlocks03
import AspisV8R17.SourceDiagonalBlocks04
import AspisV8R17.SourceDiagonalBlocks12
import AspisV8R17.SourceLowerBlocks23
import AspisV8R17.SourceLowerBlocks24
import AspisV8R17.SourceLowerBlocks25
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block112_eq : matrixWindow sourceMatrix 187 2 = BlockDeterminants.block11 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 187 187 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block29_entry0_0
    ·
      change sourceMatrix 187 188 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block29_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 188 187 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block29_entry1_0
    ·
      change sourceMatrix 188 188 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block29_entry1_1
theorem block112_unit : IsUnit (matrixWindow sourceMatrix 187 2).det := by
  rw [block112_eq]
  exact BlockDeterminants.block11_det_isUnit
theorem block112_lower : ∀ (i : Fin 25) (j : Fin 2),
    sourceMatrix (187+2+i.val) (187+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (189+i.val) 187 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column48_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (189+i.val) 188 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column49_lower 1073741824 2 13 11 (-7) i
#print axioms block112_eq
#print axioms block112_unit
#print axioms block112_lower

theorem block113_eq : matrixWindow sourceMatrix 189 2 = BlockDeterminants.block18 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 189 189 = 1879048192
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block32_entry0_0
    ·
      change sourceMatrix 189 190 = 805306369
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block32_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 190 189 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block32_entry1_0
    ·
      change sourceMatrix 190 190 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block32_entry1_1
theorem block113_unit : IsUnit (matrixWindow sourceMatrix 189 2).det := by
  rw [block113_eq]
  exact BlockDeterminants.block18_det_isUnit
theorem block113_lower : ∀ (i : Fin 23) (j : Fin 2),
    sourceMatrix (189+2+i.val) (189+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (191+i.val) 189 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column54_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (191+i.val) 190 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column55_lower 1073741824 2 13 11 (-7) i
#print axioms block113_eq
#print axioms block113_unit
#print axioms block113_lower

theorem block114_eq : matrixWindow sourceMatrix 191 2 = BlockDeterminants.block6 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 191 191 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block36_entry0_0
    ·
      change sourceMatrix 191 192 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block36_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 192 191 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block36_entry1_0
    ·
      change sourceMatrix 192 192 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block36_entry1_1
theorem block114_unit : IsUnit (matrixWindow sourceMatrix 191 2).det := by
  rw [block114_eq]
  exact BlockDeterminants.block6_det_isUnit
theorem block114_lower : ∀ (i : Fin 21) (j : Fin 2),
    sourceMatrix (191+2+i.val) (191+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (193+i.val) 191 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column60_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (193+i.val) 192 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column61_lower 1073741824 2 13 11 (-7) i
#print axioms block114_eq
#print axioms block114_unit
#print axioms block114_lower

theorem block115_eq : matrixWindow sourceMatrix 193 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 193 193 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block39_entry0_0
    ·
      change sourceMatrix 193 194 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block39_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 194 193 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block39_entry1_0
    ·
      change sourceMatrix 194 194 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block39_entry1_1
theorem block115_unit : IsUnit (matrixWindow sourceMatrix 193 2).det := by
  rw [block115_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block115_lower : ∀ (i : Fin 19) (j : Fin 2),
    sourceMatrix (193+2+i.val) (193+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (195+i.val) 193 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column66_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (195+i.val) 194 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column67_lower 1073741824 2 13 11 (-7) i
#print axioms block115_eq
#print axioms block115_unit
#print axioms block115_lower

theorem block116_eq : matrixWindow sourceMatrix 195 1 = BlockDeterminants.block21 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 195 195 = 11
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block46_entry0_0
theorem block116_unit : IsUnit (matrixWindow sourceMatrix 195 1).det := by
  rw [block116_eq]
  exact BlockDeterminants.block21_det_isUnit
theorem block116_lower : ∀ (i : Fin 18) (j : Fin 1),
    sourceMatrix (195+1+i.val) (195+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (196+i.val) 195 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column77_lower 1073741824 2 13 11 (-7) i
#print axioms block116_eq
#print axioms block116_unit
#print axioms block116_lower

theorem block117_eq : matrixWindow sourceMatrix 196 2 = BlockDeterminants.block22 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 196 196 = 1879048192
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block49_entry0_0
    ·
      change sourceMatrix 196 197 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block49_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 197 196 = 805306369
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block49_entry1_0
    ·
      change sourceMatrix 197 197 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block49_entry1_1
theorem block117_unit : IsUnit (matrixWindow sourceMatrix 196 2).det := by
  rw [block117_eq]
  exact BlockDeterminants.block22_det_isUnit
theorem block117_lower : ∀ (i : Fin 16) (j : Fin 2),
    sourceMatrix (196+2+i.val) (196+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (198+i.val) 196 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column80_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (198+i.val) 197 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column81_lower 1073741824 2 13 11 (-7) i
#print axioms block117_eq
#print axioms block117_unit
#print axioms block117_lower

theorem block118_eq : matrixWindow sourceMatrix 198 2 = BlockDeterminants.block6 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 198 198 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block132_entry0_0
    ·
      change sourceMatrix 198 199 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block132_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 199 198 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block132_entry1_0
    ·
      change sourceMatrix 199 199 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block132_entry1_1
theorem block118_unit : IsUnit (matrixWindow sourceMatrix 198 2).det := by
  rw [block118_eq]
  exact BlockDeterminants.block6_det_isUnit
theorem block118_lower : ∀ (i : Fin 14) (j : Fin 2),
    sourceMatrix (198+2+i.val) (198+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (200+i.val) 198 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column212_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (200+i.val) 199 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column213_lower 1073741824 2 13 11 (-7) i
#print axioms block118_eq
#print axioms block118_unit
#print axioms block118_lower

theorem block119_eq : matrixWindow sourceMatrix 200 1 = BlockDeterminants.block0 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 200 200 = 1073741827
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block0_entry0_0
theorem block119_unit : IsUnit (matrixWindow sourceMatrix 200 1).det := by
  rw [block119_eq]
  exact BlockDeterminants.block0_det_isUnit
theorem block119_lower : ∀ (i : Fin 13) (j : Fin 1),
    sourceMatrix (200+1+i.val) (200+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (201+i.val) 200 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column0_lower 1073741824 2 13 11 (-7) i
#print axioms block119_eq
#print axioms block119_unit
#print axioms block119_lower

end AspisV8R17.SourceMinor.Windows
