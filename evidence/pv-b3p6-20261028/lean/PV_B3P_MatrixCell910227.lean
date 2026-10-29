import PV_B3P_MatrixCell9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem accumulation_store9_1_0 (sums : Matrix3x3) (left right : U32) :
    matrix_cell sums 1#usize 0#usize left right =
      .ok (matrix_put sums 1#usize 0#usize (by change 1<3; omega) (by change 0<3; omega) left right) :=
  matrix_cell_result sums 1#usize 0#usize (by change 1<3; omega) (by change 0<3; omega) left right
#print axioms accumulation_store9_1_0
end PV_B3P_Binding9227
