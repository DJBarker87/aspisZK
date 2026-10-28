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
  have claims : AspisS1NativeCompact.r1_wire.CLAIMS = ok 87#usize := by
    simpa only [AspisS1NativeCompact.r1_wire.CLAIMS, AspisS1NativeCompact.r1_wire.POINTS,
      AspisS1NativeCompact.r1_wire.LANES, AspisR1RowShape.r1_wire.CLAIMS,
      AspisR1RowShape.r1_wire.POINTS, AspisR1RowShape.r1_wire.LANES] using
      AspisR1.ExtractedRowShape.claims_eq
  unfold NCO_Reference.row_shape_ref AspisS1NativeCompact.r1_wire.row_shape
  simp only [claims, AspisS1NativeCompact.r1_wire.LANES, bind_tc_ok,
    AspisR1.ExtractedRowShape.claims_plus_lanes_eq,
    AspisR1.ExtractedRowShape.claims_payload_eq,
    AspisR1.ExtractedRowShape.lanes_payload_eq,
    AspisR1.ExtractedRowShape.sumcheck_payload_eq]

#print axioms compact_row
#print axioms row_shape
end NCO_ScalarBridge
