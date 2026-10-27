import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix066
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_wire.record`.
Recursive calls remain the original extracted calls. -/
def continueAfter (row : Std.U8) (payload : Slice Std.U8) (out : Payload (r1_wire.row_shape row)) : Result (core.result.Result (alloc.vec.Vec Std.U8) r1_wire.Error) := do
  let o := out
  let r ← core.option.Option.ok_or o r1_wire.Error.InvalidRow
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (tag, size) := val
    let i := Slice.len payload
    if i != size
    then ok (core.result.Result.Err (r1_wire.Error.Length row))
    else
      let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add 5#usize size)
      let out := alloc.vec.Vec.with_capacity Std.U8 i1
      let out1 ← alloc.vec.Vec.push out tag
      let i2 ← Aeneas.Std.lift (UScalar.cast .U32 size)
      let a ← Aeneas.Std.lift (core.num.U32.to_le_bytes i2)
      let s ← Aeneas.Std.lift (Array.to_slice a)
      let out2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 s
      let out3 ←
        alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out2 payload
      let s1 := alloc.vec.Vec.deref out3
      let r1 ← host_wire.parse_record row s1
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        ok (core.result.Result.Ok out3)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame r1_wire.Error) residual


end R1Z.PV_RE_ComposedSuffix066
pv_composed_source_contexts ProverRwFull.host_wire.record
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix066.continueAfter
