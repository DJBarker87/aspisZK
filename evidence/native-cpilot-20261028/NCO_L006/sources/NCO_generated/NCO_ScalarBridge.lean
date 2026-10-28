import NCO_Reference.Funs
import S1NativeCompactModelV1
import ExtractedRowShape
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_ScalarBridge

theorem compact_row (row : U8) :
    NCO_Reference.compact_row_ref row = AspisS1NativeCompact.compact.compact_row row := by
  rfl

theorem row_shape (row : U8) :
    NCO_Reference.row_shape_ref row = AspisS1NativeCompact.r1_wire.row_shape row := by
  have same : AspisS1NativeCompact.r1_wire.row_shape row =
      AspisR1RowShape.r1_wire.row_shape row := by
    unfold AspisS1NativeCompact.r1_wire.row_shape AspisR1RowShape.r1_wire.row_shape
    unfold AspisS1NativeCompact.r1_wire.CLAIMS AspisS1NativeCompact.r1_wire.POINTS
      AspisS1NativeCompact.r1_wire.LANES AspisR1RowShape.r1_wire.CLAIMS
      AspisR1RowShape.r1_wire.POINTS AspisR1RowShape.r1_wire.LANES
    rfl
  rw [same, AspisR1.ExtractedRowShape.row_shape_eq_table]
  simp [NCO_Reference.row_shape_ref, AspisR1.ExtractedRowShape.table]
  split_ifs <;> first | rfl | omega

#print axioms compact_row
#print axioms row_shape
end NCO_ScalarBridge
