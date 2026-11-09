import AspisV8R19.InverseFieldSlice

/-! Exact generated declarations from the overflow-checked R62 source extraction.
Only imports and namespace framing are narrowed; the source audit checks all
nine declarations including the extraction-only entry point. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR64Field

@[reducible]
def field.M31 := Std.U32

/-- [aspis_core::field::P]
    Source: 'field.rs', lines 16:0-16:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::reduce_u64]:
    Source: 'field.rs', lines 28:0-41:1 -/
def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then x3 - field.P
  else ok x3

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'field.rs', lines 77:4-85:5
    Visibility: public -/
def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  if self < field.P
  then
    if rhs < field.P
    then
      let i ← lift (UScalar.cast .U64 self)
      let i1 ← lift (UScalar.cast .U64 rhs)
      let x ← i * i1
      let i2 ← lift (UScalar.cast .U64 field.P)
      let i3 ← lift (x &&& i2)
      let i4 ← x >>> 31#i32
      let s ← i3 + i4
      let i5 ← lift (UScalar.cast .U64 field.P)
      if s >= i5
      then
        let i6 ← lift (UScalar.cast .U64 field.P)
        let i7 ← s - i6
        let i8 ← lift (UScalar.cast .U32 i7)
        ok i8
      else let i6 ← lift (UScalar.cast .U32 s)
           ok i6
    else
      let i ← lift (UScalar.cast .U64 self)
      let i1 ← lift (UScalar.cast .U64 rhs)
      let i2 ← i * i1
      let i3 ← field.reduce_u64 i2
      ok i3
  else
    let i ← lift (UScalar.cast .U64 self)
    let i1 ← lift (UScalar.cast .U64 rhs)
    let i2 ← i * i1
    let i3 ← field.reduce_u64 i2
    ok i3

/-- [aspis_core::field::square_n]: loop body 0:
    Source: 'field.rs', lines 45:4-47:5 -/
@[rust_loop_body]
def field.square_n_loop.body
  (iter : core.ops.range.Range Std.Usize) (value : field.M31) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × field.M31)
    field.M31)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done value)
  | some _ =>
    let value1 ← field.M31.mul value value
    ok (cont (iter1, value1))

/-- [aspis_core::field::square_n]: loop 0:
    Source: 'field.rs', lines 45:4-47:5 -/
@[rust_loop]
def field.square_n_loop
  (iter : core.ops.range.Range Std.Usize) (value : field.M31) :
  Result field.M31
  := do
  loop
    (fun (iter1, value1) => field.square_n_loop.body iter1 value1)
    (iter, value)

/-- [aspis_core::field::square_n]:
    Source: 'field.rs', lines 44:0-49:1 -/
@[reducible]
def field.square_n
  (value : field.M31) (count : Std.Usize) : Result field.M31 := do
  field.square_n_loop { start := 0#usize, «end» := count } value

/-- [aspis_core::field::{aspis_core::field::M31}::inv]:
    Source: 'field.rs', lines 157:4-173:5
    Visibility: public -/
def field.M31.inv (self : field.M31) : Result field.M31 := do
  massert (self != 0#u32)
  let m ← field.M31.mul self self
  let t2 ← field.M31.mul m self
  let m1 ← field.square_n t2 2#usize
  let t4 ← field.M31.mul m1 t2
  let m2 ← field.square_n t4 4#usize
  let t8 ← field.M31.mul m2 t4
  let m3 ← field.square_n t8 8#usize
  let t16 ← field.M31.mul m3 t8
  let m4 ← field.square_n t16 8#usize
  let t24 ← field.M31.mul m4 t8
  let m5 ← field.square_n t24 4#usize
  let t28 ← field.M31.mul m5 t4
  let m6 ← field.M31.mul t28 t28
  let t29 ← field.M31.mul m6 self
  let t30 ← field.M31.mul t29 t29
  let m7 ← field.M31.mul t30 t30
  field.M31.mul m7 self

/-- [aspis_core::inverse_probe]:
    Source: 'lib.rs', lines 4:0-6:1
    Visibility: public -/
def inverse_probe (x : field.M31) : Result field.M31 := do
  field.M31.inv x

end AspisR64Field

