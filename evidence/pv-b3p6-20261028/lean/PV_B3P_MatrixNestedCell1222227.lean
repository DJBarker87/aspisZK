import PV_B3P_MatrixNested12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 Result
set_option autoImplicit false
theorem source_matrix_cell12_2_2 (left right : Channels12) (sums : Matrix3x3) :
    source_channel12 left right 2#usize sums 2#usize =
      matrix_cell sums 2#usize 2#usize (get3_2 (get3_2 left)) (get3_2 (get3_2 right)) :=
  source_channel_binding12 left right 2#usize 2#usize (by change 2<3; omega) (by change 2<3; omega) sums
#print axioms source_matrix_cell12_2_2
end PV_B3P_Binding12227
