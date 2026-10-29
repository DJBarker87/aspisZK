import PV_B3P_MatrixNested12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 Result
set_option autoImplicit false
theorem source_matrix_cell12_1_1 (left right : Channels12) (sums : Matrix3x3) :
    source_channel12 left right 1#usize sums 1#usize =
      matrix_cell sums 1#usize 1#usize (get3_1 (get3_1 left)) (get3_1 (get3_1 right)) :=
  source_channel_binding12 left right 1#usize 1#usize (by change 1<3; omega) (by change 1<3; omega) sums
#print axioms source_matrix_cell12_1_1
end PV_B3P_Binding12227
