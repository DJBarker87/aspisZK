import PV_B3P_MatrixNested12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 Result
set_option autoImplicit false
theorem source_matrix_cell12_0_0 (left right : Channels12) (sums : Matrix3x3) :
    source_channel12 left right 0#usize sums 0#usize =
      matrix_cell sums 0#usize 0#usize (get3_0 (get3_0 left)) (get3_0 (get3_0 right)) :=
  source_channel_binding12 left right 0#usize 0#usize (by change 0<3; omega) (by change 0<3; omega) sums
#print axioms source_matrix_cell12_0_0
end PV_B3P_Binding12227
