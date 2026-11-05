import NGX_ParseRecord
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NGX_RecordAt
abbrev Error := AspisR1PrefixAggregateParser.r1_wire.Error
abbrev Parser := U8→Slice U8→Result (core.result.Result (Slice U8) Error)

def computation (parse : Parser) (bytes : Slice U8) (row : U8) (offset : Usize) :
 Result (core.result.Result (Slice U8×Usize) Error) := do
 let shape ← AspisR1PrefixAggregateParser.r1_wire.row_shape row
 let (_,size) ← core.option.Option.unwrap shape
 let length ← 5#usize+size
 let next ← offset+length
 let candidate ← core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes {start:=offset,«end»:=next}
 let result ← AspisR1PrefixAggregateParser.core.option.Option.ok_or candidate (AspisR1PrefixAggregateParser.r1_wire.Error.Length row)
 let cf ← core.result.Result.Insts.CoreOpsTry.branch result
 match cf with
 | .Continue framed => do
  let parsed ← parse row framed
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch parsed
  match cf1 with
  | .Continue _ => ok (.Ok (framed,next))
  | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Slice U8×Usize) (core.convert.FromSame Error) residual
 | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (Slice U8×Usize) (core.convert.FromSame Error) residual

theorem source (bytes : Slice U8) (row : U8) (offset : Usize) :
 AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes row offset =
 computation AspisR1PrefixAggregateParser.r1_wire.parse_record bytes row offset := by rfl

theorem frame_domain (row tag : U8) (size : Usize) (framed : Slice U8)
 (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size)))
 (length : framed.val.length=5+size.val) :
 5≤framed.val.length ∧ framed.val.length≤3717 := by
 have bound := (NFU_RowDomains.parser_shape row tag size shape).1
 omega

theorem end_bound (offset length : Nat) (hoffset : offset≤57607) (hlength : length≤3717) :
 offset+length≤61324 := by omega
#print axioms source
#print axioms frame_domain
#print axioms end_bound
end AspisR1.NGX_RecordAt
