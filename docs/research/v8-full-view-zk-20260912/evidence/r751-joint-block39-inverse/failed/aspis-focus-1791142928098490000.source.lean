/- Aggregates the independently checked 39 rows of the SCC-6 candidate B*A.
This is a finite candidate-block result; it does not bind the matrix to source
execution or close the privacy/security argument. -/
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R749JointBlock39Row28
import AspisV8R19.R750JointBlock39Rows01
import AspisV8R19.R750JointBlock39Rows02
import AspisV8R19.R750JointBlock39Rows03
import AspisV8R19.R750JointBlock39Rows04
import AspisV8R19.R750JointBlock39Rows05
import AspisV8R19.R750JointBlock39Rows06
import AspisV8R19.R750JointBlock39Rows07
import AspisV8R19.R750JointBlock39Rows08
import AspisV8R19.R750JointBlock39Rows09
import AspisV8R19.R750JointBlock39Rows10
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace R751JointBlock39Inverse
open R747JointBlock39Preflight

theorem left_inverse : B * A = 1 := by
  ext i j
  fin_cases i
  · exact R750JointBlock39Rows01.row_0 j
  · exact R750JointBlock39Rows01.row_1 j
  · exact R750JointBlock39Rows01.row_2 j
  · exact R750JointBlock39Rows02.row_3 j
  · exact R750JointBlock39Rows02.row_4 j
  · exact R750JointBlock39Rows02.row_5 j
  · exact R750JointBlock39Rows02.row_6 j
  · exact R750JointBlock39Rows03.row_7 j
  · exact R750JointBlock39Rows03.row_8 j
  · exact R750JointBlock39Rows03.row_9 j
  · exact R750JointBlock39Rows03.row_10 j
  · exact R750JointBlock39Rows04.row_11 j
  · exact R750JointBlock39Rows04.row_12 j
  · exact R750JointBlock39Rows04.row_13 j
  · exact R750JointBlock39Rows04.row_14 j
  · exact R750JointBlock39Rows05.row_15 j
  · exact R750JointBlock39Rows05.row_16 j
  · exact R750JointBlock39Rows05.row_17 j
  · exact R750JointBlock39Rows05.row_18 j
  · exact R750JointBlock39Rows06.row_19 j
  · exact R750JointBlock39Rows06.row_20 j
  · exact R750JointBlock39Rows06.row_21 j
  · exact R750JointBlock39Rows06.row_22 j
  · exact R750JointBlock39Rows07.row_23 j
  · exact R750JointBlock39Rows07.row_24 j
  · exact R750JointBlock39Rows07.row_25 j
  · exact R750JointBlock39Rows07.row_26 j
  · exact R750JointBlock39Rows08.row_27 j
  · exact R749JointBlock39Row28.row28 j
  · exact R750JointBlock39Rows08.row_29 j
  · exact R750JointBlock39Rows08.row_30 j
  · exact R750JointBlock39Rows08.row_31 j
  · exact R750JointBlock39Rows09.row_32 j
  · exact R750JointBlock39Rows09.row_33 j
  · exact R750JointBlock39Rows09.row_34 j
  · exact R750JointBlock39Rows09.row_35 j
  · exact R750JointBlock39Rows10.row_36 j
  · exact R750JointBlock39Rows10.row_37 j
  · exact R750JointBlock39Rows01.row_38 j

#print axioms left_inverse

theorem determinant_nonzero : Matrix.det A ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse left_inverse

#print axioms determinant_nonzero

end R751JointBlock39Inverse
