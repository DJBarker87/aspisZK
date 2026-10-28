import NCO_Framing
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_ParserAt

theorem reference_short (bytes : Slice U8) (row tag : U8) (offset size len end1 : Usize)
    (shape : NCO_ParserRef.row_shape_ref row = ok (some (tag,size)))
    (sum : 5#usize + size = ok len) (add : offset + len = ok end1)
    (get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start := offset, «end» := end1} = ok none) :
    NCO_ParserRef.parse_at_ref bytes row offset = ok (.Err (.Length row)) := by
  simp [NCO_ParserRef.parse_at_ref, shape, sum, add, get,
    core.option.Option.unwrap, NCO_ParserRef.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

theorem source_short (bytes : Slice U8) (row tag : U8) (offset size len end1 : Usize)
    (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok (some (tag,size)))
    (sum : 5#usize + size = ok len) (add : offset + len = ok end1)
    (get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start := offset, «end» := end1} = ok none) :
    AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes row offset = ok (.Err (.Length row)) := by
  simp [AspisR1PrefixAggregateParser.r1_wire.parse_record_at, shape, sum, add, get,
    core.option.Option.unwrap,
    AspisR1PrefixAggregateParser.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

#print axioms reference_short
#print axioms source_short
end NCO_ParserAt
