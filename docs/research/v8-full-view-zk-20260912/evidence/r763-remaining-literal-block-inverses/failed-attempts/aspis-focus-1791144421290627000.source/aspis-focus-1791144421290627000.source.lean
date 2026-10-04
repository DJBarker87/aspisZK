import AspisV8R19.R752SCC04Matrix
import AspisV8R19.R752SCC04Rows01
import AspisV8R19.R752SCC04Rows02
import AspisV8R19.R752SCC04Rows03
import AspisV8R19.R752SCC04Rows04
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace R752SCC04Inverse
open R752SCC04Matrix

local instance : Fact (1 < 2147483647) := ⟨by decide⟩

theorem left_inverse : B_scc * A_scc = 1 := by
  ext i j
  fin_cases i
  · simpa [Matrix.one_apply] using R752SCC04Rows01.row_0 j
  · simpa [Matrix.one_apply] using R752SCC04Rows01.row_1 j
  · simpa [Matrix.one_apply] using R752SCC04Rows01.row_2 j
  · simpa [Matrix.one_apply] using R752SCC04Rows01.row_3 j
  · simpa [Matrix.one_apply] using R752SCC04Rows02.row_4 j
  · simpa [Matrix.one_apply] using R752SCC04Rows02.row_5 j
  · simpa [Matrix.one_apply] using R752SCC04Rows02.row_6 j
  · simpa [Matrix.one_apply] using R752SCC04Rows02.row_7 j
  · simpa [Matrix.one_apply] using R752SCC04Rows03.row_8 j
  · simpa [Matrix.one_apply] using R752SCC04Rows03.row_9 j
  · simpa [Matrix.one_apply] using R752SCC04Rows03.row_10 j
  · simpa [Matrix.one_apply] using R752SCC04Rows03.row_11 j
  · simpa [Matrix.one_apply] using R752SCC04Rows04.row_12 j
  · simpa [Matrix.one_apply] using R752SCC04Rows04.row_13 j
  · simpa [Matrix.one_apply] using R752SCC04Rows04.row_14 j
  · simpa [Matrix.one_apply] using R752SCC04Rows04.row_15 j
theorem determinant_isUnit : IsUnit (Matrix.det A_scc) :=
  Matrix.isUnit_det_of_left_inverse left_inverse

#print axioms determinant_isUnit

#print axioms left_inverse

theorem determinant_nonzero : Matrix.det A_scc ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse left_inverse

#print axioms determinant_nonzero

end R752SCC04Inverse
