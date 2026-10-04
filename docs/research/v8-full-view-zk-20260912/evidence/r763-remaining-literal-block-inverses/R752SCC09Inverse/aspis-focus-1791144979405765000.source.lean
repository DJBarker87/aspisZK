import AspisV8R19.R752SCC09Matrix
import AspisV8R19.R752SCC09Rows01
import AspisV8R19.R752SCC09Rows02
import AspisV8R19.R752SCC09Rows03
import AspisV8R19.R752SCC09Rows04
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace R752SCC09Inverse
open R752SCC09Matrix

local instance : Fact (1 < 2147483647) := ⟨by decide⟩

theorem left_inverse : B_scc * A_scc = 1 := by
  ext i j
  fin_cases i
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_0
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_1
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_2
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_3
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_4
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_5
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_6
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_7
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_8
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_9
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_10
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_11
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_12
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_13
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_14
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_0_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_0
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_1
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_2
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_3
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_4
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_5
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_6
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_7
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_8
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_9
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_10
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_11
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_12
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_13
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_14
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_1_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_0
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_1
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_2
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_3
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_4
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_5
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_6
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_7
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_8
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_9
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_10
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_11
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_12
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_13
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_14
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_2_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_0
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_1
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_2
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_3
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_4
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_5
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_6
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_7
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_8
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_9
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_10
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_11
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_12
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_13
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_14
    · simpa [Matrix.one_apply] using R752SCC09Rows01.cell_3_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_0
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_1
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_2
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_3
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_4
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_5
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_6
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_7
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_8
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_9
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_10
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_11
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_12
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_13
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_14
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_4_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_0
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_1
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_2
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_3
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_4
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_5
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_6
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_7
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_8
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_9
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_10
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_11
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_12
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_13
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_14
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_5_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_0
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_1
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_2
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_3
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_4
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_5
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_6
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_7
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_8
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_9
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_10
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_11
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_12
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_13
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_14
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_6_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_0
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_1
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_2
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_3
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_4
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_5
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_6
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_7
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_8
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_9
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_10
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_11
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_12
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_13
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_14
    · simpa [Matrix.one_apply] using R752SCC09Rows02.cell_7_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_0
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_1
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_2
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_3
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_4
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_5
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_6
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_7
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_8
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_9
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_10
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_11
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_12
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_13
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_14
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_8_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_0
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_1
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_2
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_3
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_4
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_5
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_6
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_7
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_8
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_9
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_10
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_11
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_12
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_13
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_14
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_9_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_0
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_1
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_2
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_3
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_4
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_5
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_6
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_7
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_8
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_9
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_10
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_11
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_12
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_13
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_14
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_10_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_0
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_1
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_2
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_3
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_4
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_5
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_6
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_7
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_8
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_9
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_10
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_11
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_12
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_13
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_14
    · simpa [Matrix.one_apply] using R752SCC09Rows03.cell_11_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_0
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_1
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_2
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_3
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_4
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_5
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_6
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_7
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_8
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_9
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_10
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_11
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_12
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_13
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_14
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_12_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_0
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_1
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_2
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_3
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_4
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_5
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_6
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_7
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_8
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_9
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_10
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_11
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_12
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_13
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_14
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_13_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_0
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_1
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_2
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_3
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_4
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_5
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_6
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_7
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_8
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_9
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_10
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_11
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_12
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_13
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_14
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_14_15
  · fin_cases j
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_0
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_1
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_2
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_3
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_4
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_5
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_6
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_7
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_8
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_9
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_10
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_11
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_12
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_13
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_14
    · simpa [Matrix.one_apply] using R752SCC09Rows04.cell_15_15
theorem determinant_isUnit : IsUnit (Matrix.det A_scc) :=
  Matrix.isUnit_det_of_left_inverse left_inverse

#print axioms determinant_isUnit

#print axioms left_inverse

theorem determinant_nonzero : Matrix.det A_scc ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse left_inverse

#print axioms determinant_nonzero

end R752SCC09Inverse
