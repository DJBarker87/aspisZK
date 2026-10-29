import PV_B3P_MatrixNestedBinding12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 Result
set_option autoImplicit false

def source_accumulate12 (sums : Matrix3x3) (right : aspis_core.field.QM31)
    (left : reference_field.PreparedQm31Multiplier) : Result Matrix3x3 := do
  let right_sum ← aspis_core.field.CM31.add right.c0 right.c1
  let m ← aspis_core.field.M31.add right.c0.a right.c0.b
  let m1 ← aspis_core.field.M31.add right.c1.a right.c1.b
  let m2 ← aspis_core.field.M31.add right_sum.a right_sum.b
  let channels := Array.make 3#usize [
    Array.make 3#usize [right.c0.a,right.c0.b,m] (by simp),
    Array.make 3#usize [right.c1.a,right.c1.b,m1] (by simp),
    Array.make 3#usize [right_sum.a,right_sum.b,m2] (by simp)] (by simp)
  source_nested12 left.components channels sums

attribute [local irreducible] aspis_core.field.CM31.add aspis_core.field.M31.add
  matrix_cell source_nested12

theorem accumulate_nested_binding12 (sums : Matrix3x3) (right : aspis_core.field.QM31)
    (left : reference_field.PreparedQm31Multiplier) :
    reference_field.accumulate_prepared227 sums right left = source_accumulate12 sums right left := by
  rw [accumulate_nine_cell_binding10]
  unfold accumulate_nine_cells10 source_accumulate12
  apply bind_equal9
  intro right_sum
  apply bind_equal9
  intro m
  apply bind_equal9
  intro m1
  apply bind_equal9
  intro m2
  rw [source_nested_binding12]
  unfold source_nine12
  rfl

#print axioms accumulate_nested_binding12
end PV_B3P_Binding12227
