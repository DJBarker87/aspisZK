import AspisV8R19.R752SCC38Matrix
import AspisV8R19.R752SCC38Rows01
import AspisV8R19.R752SCC38Rows02
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace R752SCC38Inverse
open R752SCC38Matrix

local instance : Fact (1 < 2147483647) := ⟨by decide⟩

theorem left_inverse : B_scc * A_scc = 1 := by
  ext i j
  fin_cases i
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_0_0
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_0_1
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_0_2
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_0_3
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_0_4
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_0_5
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_0_6
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_0_7
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_1_0
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_1_1
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_1_2
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_1_3
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_1_4
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_1_5
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_1_6
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_1_7
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_2_0
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_2_1
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_2_2
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_2_3
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_2_4
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_2_5
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_2_6
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_2_7
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_3_0
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_3_1
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_3_2
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_3_3
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_3_4
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_3_5
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_3_6
    · simpa [Matrix.one_apply] using R752SCC38Rows01.cell_3_7
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_4_0
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_4_1
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_4_2
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_4_3
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_4_4
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_4_5
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_4_6
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_4_7
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_5_0
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_5_1
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_5_2
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_5_3
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_5_4
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_5_5
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_5_6
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_5_7
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_6_0
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_6_1
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_6_2
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_6_3
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_6_4
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_6_5
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_6_6
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_6_7
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_7_0
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_7_1
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_7_2
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_7_3
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_7_4
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_7_5
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_7_6
    · simpa [Matrix.one_apply] using R752SCC38Rows02.cell_7_7
theorem determinant_isUnit : IsUnit (Matrix.det A_scc) :=
  Matrix.isUnit_det_of_left_inverse left_inverse

#print axioms determinant_isUnit

#print axioms left_inverse

theorem determinant_nonzero : Matrix.det A_scc ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse left_inverse

#print axioms determinant_nonzero

end R752SCC38Inverse
