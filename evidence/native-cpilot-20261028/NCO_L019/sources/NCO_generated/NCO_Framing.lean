import NCO_Reject
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_Framing

theorem reference_length (row tag : U8) (size total : Usize) (bs : Slice U8)
    (shape : NCO_ParserRef.row_shape_ref row = ok (some (tag,size)))
    (sum : 5#usize + size = ok total) (different : Slice.len bs ≠ total) :
    NCO_ParserRef.parse_record_ref row bs = ok (.Err (.Length row)) := by
  simp_all [NCO_ParserRef.parse_record_ref, shape, NCO_ParserRef.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch, sum, different]

theorem source_length (row tag : U8) (size total : Usize) (bs : Slice U8)
    (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok (some (tag,size)))
    (sum : 5#usize + size = ok total) (different : Slice.len bs ≠ total) :
    AspisR1PrefixAggregateParser.r1_wire.parse_record row bs = ok (.Err (.Length row)) := by
  simp_all [AspisR1PrefixAggregateParser.r1_wire.parse_record, shape,
    AspisR1PrefixAggregateParser.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch, sum, different]

def error : NCO_ParserRef.RefError → AspisR1PrefixAggregateParser.r1_wire.Error
  | .InvalidRow => .InvalidRow
  | .Length row => .Length row
  | .Tag row => .Tag row
  | .NonCanonical row value => .NonCanonical row value

def result {α : Type} : core.result.Result α NCO_ParserRef.RefError →
    core.result.Result α AspisR1PrefixAggregateParser.r1_wire.Error
  | .Ok a => .Ok a
  | .Err e => .Err (error e)

theorem length_bridge (row tag : U8) (size total : Usize) (bs : Slice U8)
    (shape : NCO_ParserRef.row_shape_ref row = ok (some (tag,size)))
    (sum : 5#usize + size = ok total) (different : Slice.len bs ≠ total) :
    (do let r ← NCO_ParserRef.parse_record_ref row bs; ok (result r)) =
      AspisR1PrefixAggregateParser.r1_wire.parse_record row bs := by
  rw [reference_length row tag size total bs shape sum different,
    source_length row tag size total bs (by simpa only [NCO_ParserShape.parser_shape] using shape) sum different]
  rfl

theorem invalid_bridge (row : U8) (bs : Slice U8) (h : 27 ≤ row.val) :
    (do let r ← NCO_ParserRef.parse_record_ref row bs; ok (result r)) =
      AspisR1PrefixAggregateParser.r1_wire.parse_record row bs := by
  rw [NCO_Reject.reference_reject row bs h, NCO_Reject.source_reject row bs h]
  rfl

#print axioms reference_length
#print axioms source_length
#print axioms length_bridge
#print axioms invalid_bridge
end NCO_Framing
