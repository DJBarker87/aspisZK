import AspisV8R17.BlockDeterminants
import AspisV8R17.SourceDiagonalBlocks02
import AspisV8R17.SourceDiagonalBlocks03
import AspisV8R17.SourceDiagonalBlocks04
import AspisV8R17.SourceLowerBlocks19
import AspisV8R17.SourceLowerBlocks20
import AspisV8R17.SourceLowerBlocks21
import AspisV8R17.SourceMatrixWindow

/-! Generated concrete source-window bindings.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Only finite cases of size at most three; named source entry and zero proofs. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.Windows
theorem block96_eq : matrixWindow sourceMatrix 159 1 = BlockDeterminants.block5 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 159 159 = 1610612737
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block24_entry0_0
theorem block96_unit : IsUnit (matrixWindow sourceMatrix 159 1).det := by
  rw [block96_eq]
  exact BlockDeterminants.block5_det_isUnit
theorem block96_lower : ∀ (i : Fin 54) (j : Fin 1),
    sourceMatrix (159+1+i.val) (159+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (160+i.val) 159 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column41_lower 1073741824 2 13 11 (-7) i
#print axioms block96_eq
#print axioms block96_unit
#print axioms block96_lower

theorem block97_eq : matrixWindow sourceMatrix 160 2 = BlockDeterminants.block13 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 160 160 = 1610612737
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block26_entry0_0
    ·
      change sourceMatrix 160 161 = 1610612738
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block26_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 161 160 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block26_entry1_0
    ·
      change sourceMatrix 161 161 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block26_entry1_1
theorem block97_unit : IsUnit (matrixWindow sourceMatrix 160 2).det := by
  rw [block97_eq]
  exact BlockDeterminants.block13_det_isUnit
theorem block97_lower : ∀ (i : Fin 52) (j : Fin 2),
    sourceMatrix (160+2+i.val) (160+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (162+i.val) 160 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column44_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (162+i.val) 161 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column45_lower 1073741824 2 13 11 (-7) i
#print axioms block97_eq
#print axioms block97_unit
#print axioms block97_lower

theorem block98_eq : matrixWindow sourceMatrix 162 1 = BlockDeterminants.block0 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 162 162 = 1073741827
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block28_entry0_0
theorem block98_unit : IsUnit (matrixWindow sourceMatrix 162 1).det := by
  rw [block98_eq]
  exact BlockDeterminants.block0_det_isUnit
theorem block98_lower : ∀ (i : Fin 51) (j : Fin 1),
    sourceMatrix (162+1+i.val) (162+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (163+i.val) 162 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column47_lower 1073741824 2 13 11 (-7) i
#print axioms block98_eq
#print axioms block98_unit
#print axioms block98_lower

theorem block99_eq : matrixWindow sourceMatrix 163 1 = BlockDeterminants.block0 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 163 163 = 1073741827
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block31_entry0_0
theorem block99_unit : IsUnit (matrixWindow sourceMatrix 163 1).det := by
  rw [block99_eq]
  exact BlockDeterminants.block0_det_isUnit
theorem block99_lower : ∀ (i : Fin 50) (j : Fin 1),
    sourceMatrix (163+1+i.val) (163+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (164+i.val) 163 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column53_lower 1073741824 2 13 11 (-7) i
#print axioms block99_eq
#print axioms block99_unit
#print axioms block99_lower

theorem block100_eq : matrixWindow sourceMatrix 164 2 = BlockDeterminants.block4 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 164 164 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block33_entry0_0
    ·
      change sourceMatrix 164 165 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block33_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 165 164 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block33_entry1_0
    ·
      change sourceMatrix 165 165 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block33_entry1_1
theorem block100_unit : IsUnit (matrixWindow sourceMatrix 164 2).det := by
  rw [block100_eq]
  exact BlockDeterminants.block4_det_isUnit
theorem block100_lower : ∀ (i : Fin 48) (j : Fin 2),
    sourceMatrix (164+2+i.val) (164+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (166+i.val) 164 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column56_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (166+i.val) 165 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column57_lower 1073741824 2 13 11 (-7) i
#print axioms block100_eq
#print axioms block100_unit
#print axioms block100_lower

theorem block101_eq : matrixWindow sourceMatrix 166 1 = BlockDeterminants.block5 := by
  ext i j
  have hi : i = 0 := by omega
  subst i
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix 166 166 = 1610612737
  rw [sourceMatrix_at _ _ (by decide) (by decide)]
  exact DiagonalBlocks.block35_entry0_0
theorem block101_unit : IsUnit (matrixWindow sourceMatrix 166 1).det := by
  rw [block101_eq]
  exact BlockDeterminants.block5_det_isUnit
theorem block101_lower : ∀ (i : Fin 47) (j : Fin 1),
    sourceMatrix (166+1+i.val) (166+j.val) = 0 := by
  intro i j
  have hj : j = 0 := by omega
  subst j
  change sourceMatrix (167+i.val) 166 = 0
  rw [sourceMatrix_at _ _ (by omega) (by decide)]
  exact LowerBlocks.column59_lower 1073741824 2 13 11 (-7) i
#print axioms block101_eq
#print axioms block101_unit
#print axioms block101_lower

theorem block102_eq : matrixWindow sourceMatrix 167 3 = BlockDeterminants.block7 := by
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 167 167 = 1073741829
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block37_entry0_0
    ·
      change sourceMatrix 167 168 = 27
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block37_entry0_1
    ·
      change sourceMatrix 167 169 = 28
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block37_entry0_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 168 167 = 0
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block37_entry1_0
    ·
      change sourceMatrix 168 168 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block37_entry1_1
    ·
      change sourceMatrix 168 169 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block37_entry1_2
  ·
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    ·
      change sourceMatrix 169 167 = 1073741827
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block37_entry2_0
    ·
      change sourceMatrix 169 168 = 2147483625
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block37_entry2_1
    ·
      change sourceMatrix 169 169 = 2147483616
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block37_entry2_2
theorem block102_unit : IsUnit (matrixWindow sourceMatrix 167 3).det := by
  rw [block102_eq]
  exact BlockDeterminants.block7_det_isUnit
theorem block102_lower : ∀ (i : Fin 44) (j : Fin 3),
    sourceMatrix (167+3+i.val) (167+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  ·
    change sourceMatrix (170+i.val) 167 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column62_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (170+i.val) 168 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column63_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (170+i.val) 169 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column64_lower 1073741824 2 13 11 (-7) i
#print axioms block102_eq
#print axioms block102_unit
#print axioms block102_lower

theorem block103_eq : matrixWindow sourceMatrix 170 2 = BlockDeterminants.block18 := by
  ext i j
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 170 170 = 1879048192
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block40_entry0_0
    ·
      change sourceMatrix 170 171 = 805306369
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block40_entry0_1
  ·
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    ·
      change sourceMatrix 171 170 = 11
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block40_entry1_0
    ·
      change sourceMatrix 171 171 = 2147483640
      rw [sourceMatrix_at _ _ (by decide) (by decide)]
      exact DiagonalBlocks.block40_entry1_1
theorem block103_unit : IsUnit (matrixWindow sourceMatrix 170 2).det := by
  rw [block103_eq]
  exact BlockDeterminants.block18_det_isUnit
theorem block103_lower : ∀ (i : Fin 42) (j : Fin 2),
    sourceMatrix (170+2+i.val) (170+j.val) = 0 := by
  intro i j
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  ·
    change sourceMatrix (172+i.val) 170 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column68_lower 1073741824 2 13 11 (-7) i
  ·
    change sourceMatrix (172+i.val) 171 = 0
    rw [sourceMatrix_at _ _ (by omega) (by decide)]
    exact LowerBlocks.column69_lower 1073741824 2 13 11 (-7) i
#print axioms block103_eq
#print axioms block103_unit
#print axioms block103_lower

end AspisV8R17.SourceMinor.Windows
