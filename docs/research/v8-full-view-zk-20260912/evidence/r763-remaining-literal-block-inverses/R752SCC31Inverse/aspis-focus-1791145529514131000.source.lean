import AspisV8R19.R752SCC31Matrix
import AspisV8R19.R752SCC31Rows01
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace R752SCC31Inverse
open R752SCC31Matrix

local instance : Fact (1 < 2147483647) := ⟨by decide⟩

theorem left_inverse : B_scc * A_scc = 1 := by
  ext i j
  fin_cases i
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC31Rows01.cell_0_0
    · simpa [Matrix.one_apply] using R752SCC31Rows01.cell_0_1
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC31Rows01.cell_1_0
    · simpa [Matrix.one_apply] using R752SCC31Rows01.cell_1_1
theorem determinant_isUnit : IsUnit (Matrix.det A_scc) :=
  Matrix.isUnit_det_of_left_inverse left_inverse

#print axioms determinant_isUnit

#print axioms left_inverse

theorem determinant_nonzero : Matrix.det A_scc ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse left_inverse

#print axioms determinant_nonzero

end R752SCC31Inverse
