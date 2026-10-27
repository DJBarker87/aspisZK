import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Guard004
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def onTrue (logical : Slice Std.U8) (count : Std.U8) (out : alloc.vec.Vec Std.U8) (at1 : Std.Usize) (row : Std.U8) : Result (ControlFlow ((alloc.vec.Vec Std.U8) × Std.Usize × Std.U8)
    ((core.result.Result Unit compact.CodecError) × (alloc.vec.Vec Std.U8))) := do
    let (r, out1) ← host_compact.compact_semantic_row logical out row at1
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let row1 ← Aeneas.Std.lift (Std.U8.wrapping_add row 1#u8)
      ok (cont (out1, val, row1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame compact.CodecError) residual
      ok (done (r1, out1))

def onFalse (logical : Slice Std.U8) (count : Std.U8) (out : alloc.vec.Vec Std.U8) (at1 : Std.Usize) (row : Std.U8) : Result (ControlFlow ((alloc.vec.Vec Std.U8) × Std.Usize × Std.U8)
    ((core.result.Result Unit compact.CodecError) × (alloc.vec.Vec Std.U8))) := do
    let i := Slice.len logical
    if at1 != i
    then ok (done (core.result.Result.Err compact.CodecError.Length, out))
    else ok (done (core.result.Result.Ok (), out))

/-- Exact first guard of `host_compact.compact_semantic_loop.body`.
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (logical : Slice Std.U8) (count : Std.U8) (out : alloc.vec.Vec Std.U8) (at1 : Std.Usize) (row : Std.U8) :
  host_compact.compact_semantic_loop.body (logical := logical) (count := count) (out := out) (at1 := at1) (row := row) =
    (if row < count then onTrue (logical := logical) (count := count) (out := out) (at1 := at1) (row := row) else onFalse (logical := logical) (count := count) (out := out) (at1 := at1) (row := row)) := by
  rw [host_compact.compact_semantic_loop.body]
  rfl

#print axioms onTrue
#print axioms onFalse
#print axioms first
end R1Z.PV_RE_Guard004
