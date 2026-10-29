import PV_B3P_MatrixNestedRow120227
import PV_B3P_MatrixNestedRow121227
import PV_B3P_MatrixNestedRow122227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 Result
set_option autoImplicit false
def source_nine12 (left right : Channels12) (sums : Matrix3x3) : Result Matrix3x3 := do
  let s00 ← matrix_cell sums 0#usize 0#usize (get3_0 (get3_0 left)) (get3_0 (get3_0 right))
  let s01 ← matrix_cell s00 0#usize 1#usize (get3_1 (get3_0 left)) (get3_1 (get3_0 right))
  let s02 ← matrix_cell s01 0#usize 2#usize (get3_2 (get3_0 left)) (get3_2 (get3_0 right))
  let s10 ← matrix_cell s02 1#usize 0#usize (get3_0 (get3_1 left)) (get3_0 (get3_1 right))
  let s11 ← matrix_cell s10 1#usize 1#usize (get3_1 (get3_1 left)) (get3_1 (get3_1 right))
  let s12 ← matrix_cell s11 1#usize 2#usize (get3_2 (get3_1 left)) (get3_2 (get3_1 right))
  let s20 ← matrix_cell s12 2#usize 0#usize (get3_0 (get3_2 left)) (get3_0 (get3_2 right))
  let s21 ← matrix_cell s20 2#usize 1#usize (get3_1 (get3_2 left)) (get3_1 (get3_2 right))
  let s22 ← matrix_cell s21 2#usize 2#usize (get3_2 (get3_2 left)) (get3_2 (get3_2 right))
  .ok s22
theorem source_nested_binding12 (left right : Channels12) (sums : Matrix3x3) :
    source_nested12 left right sums = source_nine12 left right sums := by
  unfold source_nested12
  rw [three_loop12]
  simp only [source_matrix_row12_0,source_matrix_row12_1,source_matrix_row12_2,
    source_nine12,PV_B3P_Ordered227.bind_assoc,bind_tc_ok,bind_return12]
#print axioms source_nested_binding12
end PV_B3P_Binding12227
