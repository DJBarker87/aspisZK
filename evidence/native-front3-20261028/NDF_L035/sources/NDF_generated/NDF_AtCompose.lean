import NCO_ParserAt
set_option autoImplicit false
namespace NDF_AtCompose
open Aeneas Aeneas.Std Result

theorem reference (bytes : Slice U8) (row tag : U8) (offset size len finish : Usize)
    (shape : NCO_ParserRef.row_shape_ref row=ok (some (tag,size)))
    (sum : 5#usize+size=ok len) (add : offset+len=ok finish)
    (callee : ∀ framed : Slice U8,
      (do let r ← NCO_ParserRef.parse_record_ref row framed; ok (NCO_Framing.result r)) =
        AspisR1PrefixAggregateParser.r1_wire.parse_record row framed) :
    (do let r ← NCO_ParserRef.parse_at_ref bytes row offset; ok (NCO_Framing.result r)) =
      AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes row offset := by
  have sourceShape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size)) := by
    simpa only [NCO_ParserShape.parser_shape] using shape
  unfold NCO_ParserRef.parse_at_ref AspisR1PrefixAggregateParser.r1_wire.parse_record_at
  simp only [shape,sourceShape,bind_tc_ok,core.option.Option.unwrap,Result.ofOption,sum,add]
  dsimp only
  simp only [sum,add,bind_tc_ok]
  generalize getCall : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=offset,«end»:=finish} = selected
  cases selected with
  | fail e => rfl
  | div => rfl
  | ok selected =>
    cases selected with
    | none => rfl
    | some framed =>
      simp only [NCO_ParserRef.core.option.Option.ok_or,
        AspisR1PrefixAggregateParser.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      rw [← callee framed]
      cases reply : NCO_ParserRef.parse_record_ref row framed with
      | fail e => rfl
      | div => rfl
      | ok reply => cases reply <;> rfl

#print axioms reference
end NDF_AtCompose
