import R1Z.ProverRwP7TraceCloneInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7ReverseSource
open Aeneas Aeneas.Std Result ControlFlow Error
/-- [prover_rw_success_p7::reverse32]: loop body 0:
    Source: 'lib.rs', lines 25:1-25:59
    Visibility: public -/
@[rust_loop_body]
def reverse32_loop.body
  (x : Std.U32) (out : Std.U32) (i : Std.Usize) :
  Result (ControlFlow (Std.U32 × Std.U32 × Std.Usize) Std.U32)
  := do
  if i < 32#usize
  then
    let i1 ← lift (Std.U32.wrapping_shl out 1#u32)
    let i2 ← lift (x &&& 1#u32)
    let out1 ← lift (i1 ||| i2)
    let x1 ← lift (Std.U32.wrapping_shr x 1#u32)
    let i3 ← lift (core.num.Usize.wrapping_add i 1#usize)
    ok (cont (x1, out1, i3))
  else ok (done out)

/-- [prover_rw_success_p7::reverse32]: loop 0:
    Source: 'lib.rs', lines 25:1-25:59
    Visibility: public -/
@[rust_loop]
def reverse32_loop
  (x : Std.U32) (out : Std.U32) (i : Std.Usize) : Result Std.U32 := do
  loop
    (fun (x1, out1, i1) => reverse32_loop.body x1 out1 i1)
    (x, out, i)

/-- [prover_rw_success_p7::reverse32]:
    Source: 'lib.rs', lines 23:0-27:1
    Visibility: public -/
@[reducible]
def reverse32 (x : Std.U32) : Result Std.U32 := do
  reverse32_loop x 0#u32 0#usize

end R1Z.ProverRwP7ReverseSource
