import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue052
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_compact.compact_semantic_row`.
Recursive calls remain the original extracted calls. -/
def continueAfter (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8) (row : Std.U8) (at1 : Std.Usize) (out : Payload (r1_wire.row_shape row)) : Result ((core.result.Result Std.Usize compact.CodecError) × (alloc.vec.Vec
    Std.U8)) := do
  let o := out
  let r ← core.option.Option.ok_or o compact.CodecError.Length
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (_, size) := val
    let i ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 5#usize)
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) logical { start := at1, «end» := i }
    let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s
    let at2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 5#usize)
    let b ← host_compact.compact_row row
    if b
    then
      let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add at2 size)
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) logical
          { start := at2, «end» := i1 }
      let (r1, out2) ← host_compact.compact_values s1 out1
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at2 size)
        ok (core.result.Result.Ok i2, out2)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Std.Usize (core.convert.FromSame compact.CodecError) residual
        ok (r2, out2)
    else
      let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add at2 size)
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) logical
          { start := at2, «end» := i1 }
      let out2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 s1
      let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at2 size)
      ok (core.result.Result.Ok i2, out2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Std.Usize (core.convert.FromSame compact.CodecError) residual
    ok (r1, out)

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8) (row : Std.U8) (at1 : Std.Usize) :
    host_compact.compact_semantic_row (logical := logical) (out := out) (row := row) (at1 := at1) =
      (r1_wire.row_shape row >>= fun out => continueAfter (logical := logical) (out := out) (row := row) (at1 := at1) out) := by
  rw [host_compact.compact_semantic_row]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8) (row : Std.U8) (at1 : Std.Usize) (out : Payload (r1_wire.row_shape row))
    (h : (r1_wire.row_shape row) = .ok out) :
    host_compact.compact_semantic_row (logical := logical) (out := out) (row := row) (at1 := at1) = continueAfter (logical := logical) (out := out) (row := row) (at1 := at1) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8) (row : Std.U8) (at1 : Std.Usize) (e : Error)
    (h : (r1_wire.row_shape row) = .fail e) :
    host_compact.compact_semantic_row (logical := logical) (out := out) (row := row) (at1 := at1) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (logical : Slice Std.U8) (out : alloc.vec.Vec Std.U8) (row : Std.U8) (at1 : Std.Usize)
    (h : (r1_wire.row_shape row) = .div) :
    host_compact.compact_semantic_row (logical := logical) (out := out) (row := row) (at1 := at1) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue052
