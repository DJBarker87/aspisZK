import PV_B3P_MatrixNestedCell1200227
import PV_B3P_MatrixNestedCell1201227
import PV_B3P_MatrixNestedCell1202227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 Result
set_option autoImplicit false
theorem source_matrix_row12_0 (left right : Channels12) (sums : Matrix3x3) :
    source_component12 left right 0#usize sums = (do
      let s0 ← matrix_cell sums 0#usize 0#usize (get3_0 (get3_0 left)) (get3_0 (get3_0 right))
      let s1 ← matrix_cell s0 0#usize 1#usize (get3_1 (get3_0 left)) (get3_1 (get3_0 right))
      matrix_cell s1 0#usize 2#usize (get3_2 (get3_0 left)) (get3_2 (get3_0 right))) := by
  unfold source_component12
  rw [three_loop12]
  simp only [source_matrix_cell12_0_0,source_matrix_cell12_0_1,source_matrix_cell12_0_2]
#print axioms source_matrix_row12_0
end PV_B3P_Binding12227
