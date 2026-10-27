import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix065
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_wire.parse_record`.
Recursive calls remain the original extracted calls. -/
def continueAfter (row : Std.U8) (record1 : Slice Std.U8) (out : Payload (r1_wire.row_shape row)) : Result (core.result.Result (Slice Std.U8) r1_wire.Error) := do
  let o := out
  let r ← core.option.Option.ok_or o r1_wire.Error.InvalidRow
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (tag, size) := val
    let i := Slice.len record1
    let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add 5#usize size)
    if i != i1
    then ok (core.result.Result.Err (r1_wire.Error.Length row))
    else
      let i2 ← Slice.index_usize record1 0#usize
      if i2 != tag
      then ok (core.result.Result.Err (r1_wire.Error.Tag row))
      else
        let i3 ← Slice.index_usize record1 1#usize
        let i4 ← Slice.index_usize record1 2#usize
        let i5 ← Slice.index_usize record1 3#usize
        let i6 ← Slice.index_usize record1 4#usize
        let i7 ←
          Aeneas.Std.lift (core.num.U32.from_le_bytes
            (Array.make 4#usize [ i3, i4, i5, i6 ]))
        let i8 ← Aeneas.Std.lift (UScalar.cast .Usize i7)
        if i8 != size
        then ok (core.result.Result.Err (r1_wire.Error.Length row))
        else
          let payload ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) record1
              { start := 5#usize }
          if row >= 14#u8
          then
            let r1 ← host_wire.validate_record_fields row payload
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (core.result.Result.Ok payload)
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (Slice Std.U8) (core.convert.FromSame r1_wire.Error) residual
          else ok (core.result.Result.Ok payload)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Slice Std.U8) (core.convert.FromSame r1_wire.Error) residual


end R1Z.PV_RE_ComposedSuffix065
pv_composed_source_contexts ProverRwFull.host_wire.parse_record
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix065.continueAfter
