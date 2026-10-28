import NCO_ParserShape
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_Reject

theorem source_none (row : U8) (h : 27 ≤ row.val) :
    AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok none := by
  rw [NCO_ParserShape.source_shape]
  exact AspisR1.ExtractedRowShape.row_shape_none row h

theorem reference_none (row : U8) (h : 27 ≤ row.val) :
    NCO_ParserRef.row_shape_ref row = ok none := by
  rw [NCO_ParserShape.parser_shape]
  exact source_none row h

theorem reference_reject (row : U8) (bs : Slice U8) (h : 27 ≤ row.val) :
    NCO_ParserRef.parse_record_ref row bs = ok (.Err .InvalidRow) := by
  unfold NCO_ParserRef.parse_record_ref
  rw [reference_none row h]
  rfl

theorem source_reject (row : U8) (bs : Slice U8) (h : 27 ≤ row.val) :
    AspisR1PrefixAggregateParser.r1_wire.parse_record row bs = ok (.Err .InvalidRow) := by
  unfold AspisR1PrefixAggregateParser.r1_wire.parse_record
  rw [source_none row h]
  rfl

#print axioms source_none
#print axioms reference_none
#print axioms reference_reject
#print axioms source_reject
end NCO_Reject
