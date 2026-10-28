import NCO_ScalarBridge
import NCO_ParserRef.Funs
import AspisR1PrefixAggregateParser.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_ParserShape

theorem prefix_shape (row : U8) :
    NCO_Reference.row_shape_ref row = AspisR1PrefixAggregateParser.r1_wire.row_shape row := by
  have claims : AspisR1PrefixAggregateParser.r1_wire.CLAIMS = ok 87#usize := by
    simpa only [AspisR1PrefixAggregateParser.r1_wire.CLAIMS,
      AspisR1PrefixAggregateParser.r1_wire.POINTS, AspisR1PrefixAggregateParser.r1_wire.LANES,
      AspisR1RowShape.r1_wire.CLAIMS, AspisR1RowShape.r1_wire.POINTS,
      AspisR1RowShape.r1_wire.LANES, bind_tc_ok] using AspisR1.ExtractedRowShape.claims_eq
  unfold NCO_Reference.row_shape_ref AspisR1PrefixAggregateParser.r1_wire.row_shape
  simp only [claims, AspisR1PrefixAggregateParser.r1_wire.LANES, bind_tc_ok,
    AspisR1.ExtractedRowShape.claims_plus_lanes_eq,
    AspisR1.ExtractedRowShape.claims_payload_eq,
    AspisR1.ExtractedRowShape.lanes_payload_eq,
    AspisR1.ExtractedRowShape.sumcheck_payload_eq]
  rfl

theorem parser_shape (row : U8) :
    NCO_ParserRef.row_shape_ref row = AspisR1PrefixAggregateParser.r1_wire.row_shape row := by
  exact prefix_shape row

theorem source_shape (row : U8) :
    AspisR1PrefixAggregateParser.r1_wire.row_shape row = AspisR1RowShape.r1_wire.row_shape row := by
  unfold AspisR1PrefixAggregateParser.r1_wire.row_shape AspisR1RowShape.r1_wire.row_shape
  unfold AspisR1PrefixAggregateParser.r1_wire.CLAIMS AspisR1PrefixAggregateParser.r1_wire.POINTS
    AspisR1PrefixAggregateParser.r1_wire.LANES AspisR1RowShape.r1_wire.CLAIMS
    AspisR1RowShape.r1_wire.POINTS AspisR1RowShape.r1_wire.LANES
  simp only [bind_tc_ok]

#print axioms prefix_shape
#print axioms parser_shape
#print axioms source_shape
end NCO_ParserShape
