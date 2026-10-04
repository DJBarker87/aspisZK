import AspisV8R19.R752SCC02Matrix
import AspisV8R19.R752SCC02Rows01
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace R752SCC02Inverse
open R752SCC02Matrix

local instance : Fact (1 < 2147483647) := ⟨by decide⟩

theorem left_inverse : B_scc * A_scc = 1 := by
  ext i j
  fin_cases i
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC02Rows01.cell_0_0
    · simpa [Matrix.one_apply] using R752SCC02Rows01.cell_0_1
    · simpa [Matrix.one_apply] using R752SCC02Rows01.cell_0_2
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC02Rows01.cell_1_0
    · simpa [Matrix.one_apply] using R752SCC02Rows01.cell_1_1
    · simpa [Matrix.one_apply] using R752SCC02Rows01.cell_1_2
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC02Rows01.cell_2_0
    · simpa [Matrix.one_apply] using R752SCC02Rows01.cell_2_1
    · simpa [Matrix.one_apply] using R752SCC02Rows01.cell_2_2
theorem determinant_isUnit : IsUnit (Matrix.det A_scc) :=
  Matrix.isUnit_det_of_left_inverse left_inverse

#print axioms determinant_isUnit

#print axioms left_inverse

theorem determinant_nonzero : Matrix.det A_scc ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse left_inverse

#print axioms determinant_nonzero

end R752SCC02Inverse
