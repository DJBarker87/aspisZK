import AspisR618SelectedMatrix.Funs
import AspisV8R19.R159WideBaseExecution
import AspisV8R19.R161WrappedMulExecution

set_option autoImplicit false

namespace AspisV8R19.R619MatrixExecution

open AspisV8R15.ExactTowerBase (M31Exact)
open AspisV8R19.ComplexBaseExecution (encodeBase)

/-- Exact execution of the captured selected matrix constructor on encoded
canonical base-field coordinates. -/
theorem r83_matrix_encoded (a b c d : M31Exact) :
    AspisR618SelectedMatrix.query_arithmetic.r83_matrix
      ({ c0 := { a := encodeBase a, b := encodeBase b },
         c1 := { a := encodeBase c, b := encodeBase d } } :
        AspisR618SelectedMatrix.aspis_core.field.QM31) =
    .ok (Array.make 4#usize [
      Array.make 4#usize [encodeBase a, encodeBase b, encodeBase c, encodeBase d],
      Array.make 4#usize [encodeBase (-b), encodeBase a, encodeBase (-d), encodeBase c],
      Array.make 4#usize [encodeBase (c+c-d), encodeBase (c+(d+d)), encodeBase a, encodeBase b],
      Array.make 4#usize [encodeBase (-(c+(d+d))), encodeBase (c+c-d), encodeBase (-b), encodeBase a]
    ]) := by
  simp [AspisR618SelectedMatrix.query_arithmetic.r83_matrix,
    AspisR618SelectedMatrix.aspis_core.field.M31.double,
    AspisR618SelectedMatrix.aspis_core.field.M31.add,
    AspisR618SelectedMatrix.aspis_core.field.M31.sub,
    AspisR618SelectedMatrix.aspis_core.field.M31.neg,
    AspisV8R19.R159WideBaseExecution.double_encode,
    AspisV8R19.R159WideBaseExecution.add_encode,
    AspisV8R19.R159WideBaseExecution.sub_encode,
    AspisV8R19.R161WrappedMulExecution.neg_encode]

#print axioms r83_matrix_encoded

end AspisV8R19.R619MatrixExecution
