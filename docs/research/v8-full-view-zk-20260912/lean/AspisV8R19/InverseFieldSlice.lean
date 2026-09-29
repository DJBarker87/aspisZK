import Aeneas.Std.Scalar.Bitwise
import Aeneas.Std.Scalar.Ops.Add
import Aeneas.Std.Scalar.Ops.Mul
import Aeneas.Std.Scalar.Ops.Sub
import Aeneas.Std.Core.Iter
import Aeneas.Std.Scalar.Casts
import Aeneas.Tactic.RustAttributes

/-! Byte-identical declarations from the pinned generated Types/FunsChunk04,
with narrowed imports only. Uses the full cached Aeneas runtime, not the
R17 unsigned projection. Do not import both scalar representations. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace V7Tag73CurrentHelpersOpaque

@[reducible, rust_type "aspis_core::field::M31"]
def aspis_core.field.M31 := Std.U32

@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := 2147483647#u32

@[rust_fun "aspis_core::field::reduce_u64"]
def aspis_core.field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= aspis_core.field.P
  then x3 - aspis_core.field.P
  else ok x3

@[rust_fun "aspis_core::field::{aspis_core::field::M31}::mul"]
def aspis_core.field.M31.mul
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← aspis_core.field.reduce_u64 i2
  ok i3

@[rust_loop_body, rust_fun "aspis_core::field::square_n"]
def aspis_core.field.square_n_loop.body
  (iter : core.ops.range.Range Std.Usize) (value : aspis_core.field.M31) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    aspis_core.field.M31) aspis_core.field.M31)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done value)
  | some _ =>
    let value1 ← aspis_core.field.M31.mul value value
    ok (cont (iter1, value1))

@[rust_loop, rust_fun "aspis_core::field::square_n"]
def aspis_core.field.square_n_loop
  (iter : core.ops.range.Range Std.Usize) (value : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  loop
    (fun (iter1, value1) => aspis_core.field.square_n_loop.body iter1 value1)
    (iter, value)

@[reducible, rust_fun "aspis_core::field::square_n"]
def aspis_core.field.square_n
  (value : aspis_core.field.M31) (count : Std.Usize) :
  Result aspis_core.field.M31
  := do
  aspis_core.field.square_n_loop { start := 0#usize, «end» := count } value

@[rust_fun "aspis_core::field::{aspis_core::field::M31}::inv"]
def aspis_core.field.M31.inv
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  massert (self != 0#u32)
  let m ← aspis_core.field.M31.mul self self
  let t2 ← aspis_core.field.M31.mul m self
  let m1 ← aspis_core.field.square_n t2 2#usize
  let t4 ← aspis_core.field.M31.mul m1 t2
  let m2 ← aspis_core.field.square_n t4 4#usize
  let t8 ← aspis_core.field.M31.mul m2 t4
  let m3 ← aspis_core.field.square_n t8 8#usize
  let t16 ← aspis_core.field.M31.mul m3 t8
  let m4 ← aspis_core.field.square_n t16 8#usize
  let t24 ← aspis_core.field.M31.mul m4 t8
  let m5 ← aspis_core.field.square_n t24 4#usize
  let t28 ← aspis_core.field.M31.mul m5 t4
  let m6 ← aspis_core.field.M31.mul t28 t28
  let t29 ← aspis_core.field.M31.mul m6 self
  let t30 ← aspis_core.field.M31.mul t29 t29
  let m7 ← aspis_core.field.M31.mul t30 t30
  aspis_core.field.M31.mul m7 self

end V7Tag73CurrentHelpersOpaque
