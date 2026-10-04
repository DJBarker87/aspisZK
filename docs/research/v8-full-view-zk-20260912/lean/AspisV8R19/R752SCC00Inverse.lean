import AspisV8R19.R752SCC00Matrix
import AspisV8R19.R752SCC00Rows01
import AspisV8R19.R752SCC00Rows02
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace R752SCC00Inverse
open R752SCC00Matrix

local instance : Fact (1 < 2147483647) := ⟨by decide⟩

theorem left_inverse : B_scc * A_scc = 1 := by
  ext i j
  fin_cases i
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_0_0
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_0_1
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_0_2
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_0_3
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_0_4
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_0_5
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_1_0
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_1_1
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_1_2
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_1_3
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_1_4
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_1_5
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_2_0
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_2_1
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_2_2
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_2_3
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_2_4
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_2_5
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_3_0
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_3_1
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_3_2
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_3_3
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_3_4
    · simpa [Matrix.one_apply] using R752SCC00Rows01.cell_3_5
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_4_0
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_4_1
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_4_2
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_4_3
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_4_4
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_4_5
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_5_0
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_5_1
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_5_2
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_5_3
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_5_4
    · simpa [Matrix.one_apply] using R752SCC00Rows02.cell_5_5
theorem determinant_isUnit : IsUnit (Matrix.det A_scc) :=
  Matrix.isUnit_det_of_left_inverse left_inverse

#print axioms determinant_isUnit

#print axioms left_inverse

theorem determinant_nonzero : Matrix.det A_scc ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse left_inverse

#print axioms determinant_nonzero

end R752SCC00Inverse
