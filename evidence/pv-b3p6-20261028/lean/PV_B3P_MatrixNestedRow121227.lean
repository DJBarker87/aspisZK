import PV_B3P_MatrixNestedCell1210227
import PV_B3P_MatrixNestedCell1211227
import PV_B3P_MatrixNestedCell1212227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 Result
set_option autoImplicit false
theorem source_matrix_row12_1 (left right : Channels12) (sums : Matrix3x3) :
    source_component12 left right 1#usize sums = (do
      let s0 ← matrix_cell sums 1#usize 0#usize (get3_0 (get3_1 left)) (get3_0 (get3_1 right))
      let s1 ← matrix_cell s0 1#usize 1#usize (get3_1 (get3_1 left)) (get3_1 (get3_1 right))
      matrix_cell s1 1#usize 2#usize (get3_2 (get3_1 left)) (get3_2 (get3_1 right))) := by
  unfold source_component12
  rw [three_loop12]
  simp only [source_matrix_cell12_1_0,source_matrix_cell12_1_1,source_matrix_cell12_1_2]
#print axioms source_matrix_row12_1
end PV_B3P_Binding12227
