import NCO_ParserAt
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_AtCompose

theorem reference (bytes : Slice U8) (row tag : U8) (offset size len end1 : Usize)
    (shape : NCO_ParserRef.row_shape_ref row = ok (some (tag,size)))
    (sum : 5#usize + size = ok len) (add : offset + len = ok end1)
    (callee : ∀ framed : Slice U8,
      (do let r ← NCO_ParserRef.parse_record_ref row framed; ok (NCO_Framing.result r)) =
        AspisR1PrefixAggregateParser.r1_wire.parse_record row framed) :
    (do let r ← NCO_ParserRef.parse_at_ref bytes row offset; ok (NCO_Framing.result r)) =
      AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes row offset := by
  have sourceShape : AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok (some (tag,size)) := by
    simpa only [NCO_ParserShape.parser_shape] using shape
  simp only [NCO_ParserRef.parse_at_ref,AspisR1PrefixAggregateParser.r1_wire.parse_record_at,
    shape,sourceShape,bind_tc_ok,core.option.Option.unwrap,sum,add]
  generalize getCall : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
    bytes {start:=offset,«end»:=end1} = selected
  cases selected with
  | fail e => rfl
  | div => rfl
  | ok selected =>
    cases selected with
    | none => rfl
    | some framed =>
      rw [← callee framed]
      generalize NCO_ParserRef.parse_record_ref row framed = reply
      cases reply with
      | fail e => rfl
      | div => rfl
      | ok reply => cases reply <;> rfl

#print axioms reference
end NCO_AtCompose
