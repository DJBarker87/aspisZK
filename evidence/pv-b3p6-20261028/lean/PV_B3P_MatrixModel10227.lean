import PV_B3P_MatrixStorage10227
import PV_B3P_MatrixStores9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def accumulate_nine_cells10 (sums : Array (Array U64 3#usize) 3#usize)
    (right : aspis_core.field.QM31) (left : reference_field.PreparedQm31Multiplier) : Result Matrix3x3 := do
  let right_sum ← aspis_core.field.CM31.add right.c0 right.c1
  let m ← aspis_core.field.M31.add right.c0.a right.c0.b
  let m1 ← aspis_core.field.M31.add right.c1.a right.c1.b
  let m2 ← aspis_core.field.M31.add right_sum.a right_sum.b
  let channels := Array.make 3#usize [
    Array.make 3#usize [right.c0.a,right.c0.b,m] (by simp),
    Array.make 3#usize [right.c1.a,right.c1.b,m1] (by simp),
    Array.make 3#usize [right_sum.a,right_sum.b,m2] (by simp)] (by simp)
  let sums_0 ← matrix_cell sums 0#usize 0#usize (get3_0 (get3_0 left.components)) (get3_0 (get3_0 channels))
  let sums_1 ← matrix_cell sums_0 0#usize 1#usize (get3_1 (get3_0 left.components)) (get3_1 (get3_0 channels))
  let sums_2 ← matrix_cell sums_1 0#usize 2#usize (get3_2 (get3_0 left.components)) (get3_2 (get3_0 channels))
  let sums_3 ← matrix_cell sums_2 1#usize 0#usize (get3_0 (get3_1 left.components)) (get3_0 (get3_1 channels))
  let sums_4 ← matrix_cell sums_3 1#usize 1#usize (get3_1 (get3_1 left.components)) (get3_1 (get3_1 channels))
  let sums_5 ← matrix_cell sums_4 1#usize 2#usize (get3_2 (get3_1 left.components)) (get3_2 (get3_1 channels))
  let sums_6 ← matrix_cell sums_5 2#usize 0#usize (get3_0 (get3_2 left.components)) (get3_0 (get3_2 channels))
  let sums_7 ← matrix_cell sums_6 2#usize 1#usize (get3_1 (get3_2 left.components)) (get3_1 (get3_2 channels))
  let sums_8 ← matrix_cell sums_7 2#usize 2#usize (get3_2 (get3_2 left.components)) (get3_2 (get3_2 channels))
  .ok sums_8

attribute [local irreducible] aspis_core.field.CM31.add aspis_core.field.M31.add UScalar.cast U64.wrapping_add U64.wrapping_mul Aeneas.Std.Array.set

theorem accumulate_pure_nine_cells10 (sums : Array (Array U64 3#usize) 3#usize)
    (right : aspis_core.field.QM31) (left : reference_field.PreparedQm31Multiplier) :
    accumulate_pure_storage10 sums right left = accumulate_nine_cells10 sums right left := by
  unfold accumulate_pure_storage10 accumulate_nine_cells10
  apply bind_equal9
  intro right_sum
  apply bind_equal9
  intro m
  apply bind_equal9
  intro m1
  apply bind_equal9
  intro m2
  conv_rhs => simp only [accumulation_store9_0_0, accumulation_store9_0_1, accumulation_store9_0_2, accumulation_store9_1_0, accumulation_store9_1_1, accumulation_store9_1_2, accumulation_store9_2_0, accumulation_store9_2_1, accumulation_store9_2_2,bind_tc_ok]
  unfold matrix_put get3_0 get3_1 get3_2
  rfl

theorem accumulate_nine_cell_binding10 (sums : Array (Array U64 3#usize) 3#usize)
    (right : aspis_core.field.QM31) (left : reference_field.PreparedQm31Multiplier) :
    reference_field.accumulate_prepared227 sums right left = accumulate_nine_cells10 sums right left :=
  (accumulate_storage_binding10 sums right left).trans (accumulate_pure_nine_cells10 sums right left)
#print axioms accumulate_pure_nine_cells10
#print axioms accumulate_nine_cell_binding10
end PV_B3P_Binding10227
