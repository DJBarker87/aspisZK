import Aeneas.Std.Scalar.Bitwise
import Aeneas.Std.Scalar.CoreConvertNum
import Aeneas.Std.Scalar.Ops.Add
import Aeneas.Std.Scalar.Ops.Mul
import Aeneas.Std.Scalar.Ops.Sub
import Aeneas.Tactic.RustAttributes

/-! Mechanically sliced from pinned V7 current generated Types/FunsChunk04.
Declarations and attributes are byte-identical; only imports and namespace
framing are narrowed. check_r17_field_slice.py authenticates this projection.
Do not import together with the full caller: declaration names are retained. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace V7Tag73CurrentHelpersOpaque

@[reducible, rust_type "aspis_core::field::M31"]
def aspis_core.field.M31 := Std.U32

@[rust_type "aspis_core::field::CM31"]
structure aspis_core.field.CM31 where
  a : aspis_core.field.M31
  b : aspis_core.field.M31

@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := 2147483647#u32

@[rust_fun "aspis_core::field::{aspis_core::field::M31}::add"]
def aspis_core.field.M31.add
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let s ← self + rhs
  if s >= aspis_core.field.P
  then let s1 ← s - aspis_core.field.P
       ok s1
  else ok s

@[rust_fun "aspis_core::field::{aspis_core::field::M31}::double"]
def aspis_core.field.M31.double
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  aspis_core.field.M31.add self self

@[rust_fun "aspis_core::field::{aspis_core::field::M31}::sub"]
def aspis_core.field.M31.sub
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← self + aspis_core.field.P
  let s ← i - rhs
  if s >= aspis_core.field.P
  then let s1 ← s - aspis_core.field.P
       ok s1
  else ok s

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

@[rust_fun "aspis_core::field::{aspis_core::field::M31}::reduce_u64"]
def aspis_core.field.M31.reduce_u64
  (value : Std.U64) : Result aspis_core.field.M31 := do
  let i ← aspis_core.field.reduce_u64 value
  ok i

@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::square"]
def aspis_core.field.CM31.square
  (self : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 ← lift (core.convert.num.FromU64U32.from i)
  let i6 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let i7 ← i5 + i6
  let i8 ← lift (core.convert.num.FromU64U32.from i2)
  let i9 ← i7 - i8
  let i10 ← i4 * i9
  let m ← aspis_core.field.M31.reduce_u64 i10
  let m1 ← aspis_core.field.M31.mul self.a self.b
  let m2 ← aspis_core.field.M31.double m1
  ok { a := m, b := m2 }

@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::mul"]
def aspis_core.field.CM31.mul
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  Result aspis_core.field.CM31
  := do
  let m0 ← aspis_core.field.M31.mul self.a rhs.a
  let m1 ← aspis_core.field.M31.mul self.b rhs.b
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 := rhs.a
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← i6 + i8
  let i10 ← i4 * i9
  let m2 ← aspis_core.field.M31.reduce_u64 i10
  let m ← aspis_core.field.M31.sub m0 m1
  let m3 ← aspis_core.field.M31.sub m2 m0
  let m4 ← aspis_core.field.M31.sub m3 m1
  ok { a := m, b := m4 }

end V7Tag73CurrentHelpersOpaque
