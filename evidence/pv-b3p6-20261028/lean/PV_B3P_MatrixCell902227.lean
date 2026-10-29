import PV_B3P_MatrixCell9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem accumulation_store9_0_2 (sums : Matrix3x3) (left right : U32) :
    matrix_cell sums 0#usize 2#usize left right =
      .ok (matrix_put sums 0#usize 2#usize (by change 0<3; omega) (by change 2<3; omega) left right) :=
  matrix_cell_result sums 0#usize 2#usize (by change 0<3; omega) (by change 2<3; omega) left right
#print axioms accumulation_store9_0_2
end PV_B3P_Binding9227
