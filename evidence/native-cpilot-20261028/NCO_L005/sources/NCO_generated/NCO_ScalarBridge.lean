import NCO_Reference.Funs
import S1NativeCompactModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_ScalarBridge

theorem compact_row (row : U8) :
    NCO_Reference.compact_row_ref row = AspisS1NativeCompact.compact.compact_row row := by
  rfl

theorem row_shape (row : U8) :
    NCO_Reference.row_shape_ref row = AspisS1NativeCompact.r1_wire.row_shape row := by
  unfold AspisS1NativeCompact.r1_wire.row_shape
  split
  · rfl
  · rfl
  · rfl
  · rfl
  · unfold AspisS1NativeCompact.r1_wire.CLAIMS AspisS1NativeCompact.r1_wire.POINTS
      AspisS1NativeCompact.r1_wire.LANES
    rfl
  · unfold AspisS1NativeCompact.r1_wire.LANES
    rfl
  · trace_state

#print axioms compact_row
#print axioms row_shape
end NCO_ScalarBridge
