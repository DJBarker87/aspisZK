import AspisR1PrefixAggregateParser.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_AtCut
open AspisR1PrefixAggregateParser
def invoke
  (parse : Std.U8 → Slice Std.U8 → Result (core.result.Result (Slice Std.U8) r1_wire.Error))
  (bytes : Slice Std.U8) (row : Std.U8) (offset : Std.Usize) :
  Result (core.result.Result ((Slice Std.U8) × Std.Usize) r1_wire.Error)
  := do
  let o ← r1_wire.row_shape row
  let (_, i) ← core.option.Option.unwrap o
  let length ← 5#usize + i
  let i1 ← offset + length
  let o1 ←
    core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
      bytes { start := offset, «end» := i1 }
  let r ← core.option.Option.ok_or o1 (r1_wire.Error.Length row)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← parse row val
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      ok (core.result.Result.Ok (val, i1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((Slice Std.U8) × Std.Usize) (core.convert.FromSame r1_wire.Error)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ((Slice Std.U8) × Std.Usize) (core.convert.FromSame r1_wire.Error)
      residual

theorem emitted (bytes : Slice U8) (row : U8) (offset : Usize) :
    r1_wire.parse_record_at bytes row offset = invoke r1_wire.parse_record bytes row offset := by rfl
#print axioms emitted
end NGD_AtCut
