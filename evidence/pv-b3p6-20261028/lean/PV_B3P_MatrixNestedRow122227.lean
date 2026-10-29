import PV_B3P_MatrixNestedCell1220227
import PV_B3P_MatrixNestedCell1221227
import PV_B3P_MatrixNestedCell1222227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 Result
set_option autoImplicit false
theorem source_matrix_row12_2 (left right : Channels12) (sums : Matrix3x3) :
    source_component12 left right 2#usize sums = (do
      let s0 ← matrix_cell sums 2#usize 0#usize (get3_0 (get3_2 left)) (get3_0 (get3_2 right))
      let s1 ← matrix_cell s0 2#usize 1#usize (get3_1 (get3_2 left)) (get3_1 (get3_2 right))
      matrix_cell s1 2#usize 2#usize (get3_2 (get3_2 left)) (get3_2 (get3_2 right))) := by
  unfold source_component12
  rw [three_loop12]
  simp only [source_matrix_cell12_2_0,source_matrix_cell12_2_1,source_matrix_cell12_2_2]
#print axioms source_matrix_row12_2
end PV_B3P_Binding12227
