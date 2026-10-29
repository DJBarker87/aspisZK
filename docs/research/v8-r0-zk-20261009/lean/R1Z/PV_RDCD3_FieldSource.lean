import R1Z.ProverRwFullTypes
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_FieldSource
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
structure aspis_core.field.PreparedQm31Multiplier where
  components : Array (Array aspis_core.field.M31 3#usize) 3#usize
abbrev aspis_core.field.PreparedQm31Multiplier.new.closure := Unit
abbrev aspis_core.field.PreparedQm31Multiplier.mul.closure := Unit
/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:16
    Name pattern: [aspis_core::field::P]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::ct::subtract_p]:
    Source: 'crates/aspis-core/src/field/ct.rs', lines 7:0-7:32
    Name pattern: [aspis_core::field::ct::subtract_p]
    Visibility: public -/
@[rust_fun "aspis_core::field::ct::subtract_p"]
def aspis_core.field.ct.subtract_p (x : Std.U32) : Result Std.U32 := do
  let i ← lift (UScalar.cast_fromBool .U32 (x >= aspis_core.field.P))
  let mask ← lift (core.num.U32.wrapping_sub 0#u32 i)
  let i1 ← lift (aspis_core.field.P &&& mask)
  ok (core.num.U32.wrapping_sub x i1)

/-- [aspis_core::field::ct::reduce64]:
    Source: 'crates/aspis-core/src/field/ct.rs', lines 12:0-12:30
    Name pattern: [aspis_core::field::ct::reduce64]
    Visibility: public -/
@[rust_fun "aspis_core::field::ct::reduce64"]
def aspis_core.field.ct.reduce64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i1 ← lift (x &&& i)
  let i2 ← lift (Std.U64.wrapping_shr x 31#u32)
  let x1 ← lift (Std.U64.wrapping_add i1 i2)
  let i3 ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← lift (Std.U64.wrapping_shr x1 31#u32)
  let x2 ← lift (Std.U64.wrapping_add i4 i5)
  let i6 ← lift (UScalar.cast .U32 x2)
  aspis_core.field.ct.subtract_p i6

/-- [aspis_core::field::ct::add]:
    Source: 'crates/aspis-core/src/field/ct.rs', lines 26:0-26:33
    Name pattern: [aspis_core::field::ct::add]
    Visibility: public -/
@[rust_fun "aspis_core::field::ct::add"]
def aspis_core.field.ct.add (a : Std.U32) (b : Std.U32) : Result Std.U32 := do
  let i ← lift (core.num.U32.wrapping_add a b)
  aspis_core.field.ct.subtract_p i

/-- [aspis_core::field::ct::sub]:
    Source: 'crates/aspis-core/src/field/ct.rs', lines 30:0-30:33
    Name pattern: [aspis_core::field::ct::sub]
    Visibility: public -/
@[rust_fun "aspis_core::field::ct::sub"]
def aspis_core.field.ct.sub (a : Std.U32) (b : Std.U32) : Result Std.U32 := do
  let i ← lift (core.num.U32.wrapping_add a aspis_core.field.P)
  let i1 ← lift (core.num.U32.wrapping_sub i b)
  aspis_core.field.ct.subtract_p i1

/-- [aspis_core::field::ct::neg]:
    Source: 'crates/aspis-core/src/field/ct.rs', lines 34:0-34:25
    Name pattern: [aspis_core::field::ct::neg]
    Visibility: public -/
@[rust_fun "aspis_core::field::ct::neg"]
def aspis_core.field.ct.neg (a : Std.U32) : Result Std.U32 := do
  let i ← lift (UScalar.cast_fromBool .U32 (a != 0#u32))
  let mask ← lift (core.num.U32.wrapping_sub 0#u32 i)
  let i1 ← lift (core.num.U32.wrapping_sub aspis_core.field.P a)
  ok (i1 &&& mask)

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 3279:0-3279:28
    Name pattern: [aspis_core::field::reduce_u64] -/
@[rust_fun "aspis_core::field::reduce_u64"]
def aspis_core.field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  aspis_core.field.ct.reduce64 x

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 133:4-133:37
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::mul]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::mul"]
def aspis_core.field.M31.mul
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← lift (Std.U64.wrapping_mul i i1)
  let i3 ← aspis_core.field.reduce_u64 i2
  ok i3

/-- [aspis_core::field::{aspis_core::field::M31}::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 153:4-153:40
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::reduce_u64]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::reduce_u64"]
def aspis_core.field.M31.reduce_u64
  (value : Std.U64) : Result aspis_core.field.M31 := do
  let i ← aspis_core.field.reduce_u64 value
  ok i

/-- [aspis_core::field::{aspis_core::field::M31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 3283:4-3283:39
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::add]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::add"]
def aspis_core.field.M31.add
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← aspis_core.field.ct.add self rhs
  ok i

/-- [aspis_core::field::{aspis_core::field::M31}::double]:
    Source: 'crates/aspis-core/src/field.rs', lines 183:4-183:30
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::double]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::double"]
def aspis_core.field.M31.double
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  aspis_core.field.M31.add self self

/-- [aspis_core::field::{aspis_core::field::CM31}::new]:
    Source: 'crates/aspis-core/src/field.rs', lines 271:4-271:38
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::new]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::new"]
def aspis_core.field.CM31.new
  (a : aspis_core.field.M31) (b : aspis_core.field.M31) :
  Result aspis_core.field.CM31
  := do
  ok { a, b }

/-- [aspis_core::field::{aspis_core::field::CM31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 281:4-281:39
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::add]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::add"]
def aspis_core.field.CM31.add
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  Result aspis_core.field.CM31
  := do
  let m ← aspis_core.field.M31.add self.a rhs.a
  let m1 ← aspis_core.field.M31.add self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::M31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 3285:4-3285:39
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::sub]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::sub"]
def aspis_core.field.M31.sub
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← aspis_core.field.ct.sub self rhs
  ok i

/-- [aspis_core::field::{aspis_core::field::CM31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 289:4-289:39
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::sub]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::sub"]
def aspis_core.field.CM31.sub
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  Result aspis_core.field.CM31
  := do
  let m ← aspis_core.field.M31.sub self.a rhs.a
  let m1 ← aspis_core.field.M31.sub self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::CM31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 306:4-306:39
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::mul]
    Visibility: public -/
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
  let i4 ← lift (Std.U64.wrapping_add i1 i3)
  let i5 := rhs.a
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← lift (Std.U64.wrapping_add i6 i8)
  let i10 ← lift (Std.U64.wrapping_mul i4 i9)
  let m2 ← aspis_core.field.M31.reduce_u64 i10
  let m ← aspis_core.field.M31.sub m0 m1
  let m3 ← aspis_core.field.M31.sub m2 m0
  let m4 ← aspis_core.field.M31.sub m3 m1
  ok { a := m, b := m4 }

/-- [aspis_core::field::{aspis_core::field::CM31}::square]:
    Source: 'crates/aspis-core/src/field.rs', lines 325:4-325:31
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::square]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::square"]
def aspis_core.field.CM31.square
  (self : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← lift (Std.U64.wrapping_add i1 i3)
  let i5 ← lift (core.convert.num.FromU64U32.from i)
  let i6 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let i7 ← lift (Std.U64.wrapping_add i5 i6)
  let i8 ← lift (core.convert.num.FromU64U32.from i2)
  let i9 ← lift (Std.U64.wrapping_sub i7 i8)
  let i10 ← lift (Std.U64.wrapping_mul i4 i9)
  let m ← aspis_core.field.M31.reduce_u64 i10
  let m1 ← aspis_core.field.M31.mul self.a self.b
  let m2 ← aspis_core.field.M31.double m1
  ok { a := m, b := m2 }

/-- [aspis_core::field::{aspis_core::field::CM31}::mul_m31]:
    Source: 'crates/aspis-core/src/field.rs', lines 338:4-338:42
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::mul_m31]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::mul_m31"]
def aspis_core.field.CM31.mul_m31
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.CM31
  := do
  let m ← aspis_core.field.M31.mul self.a rhs
  let m1 ← aspis_core.field.M31.mul self.b rhs
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::CM31}::double]:
    Source: 'crates/aspis-core/src/field.rs', lines 346:4-346:31
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::double]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::double"]
def aspis_core.field.CM31.double
  (self : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  aspis_core.field.CM31.add self self

/-- [aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::new::{impl core::ops::function::Fn<(aspis_core::field::CM31,), [aspis_core::field::M31; 3usize]> for aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::new::closure}::call]:
    Source: 'crates/aspis-core/src/field.rs', lines 449:22-449:39
    Name pattern: [aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::new::{core::ops::function::Fn<aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::new::closure, (aspis_core::field::CM31), [aspis_core::field::M31; 3]>}::call] -/
@[rust_fun
  "aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::new::{core::ops::function::Fn<aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::new::closure, (aspis_core::field::CM31), [aspis_core::field::M31; 3]>}::call"]
def
  aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
  (c : aspis_core.field.PreparedQm31Multiplier.new.closure)
  (tupled_args : aspis_core.field.CM31) :
  Result (Array aspis_core.field.M31 3#usize)
  := do
  let m ← aspis_core.field.M31.add tupled_args.a tupled_args.b
  ok (Array.make 3#usize [ tupled_args.a, tupled_args.b, m ])

/-- [aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::new]:
    Source: 'crates/aspis-core/src/field.rs', lines 448:4-448:35
    Name pattern: [aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::new]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::new"]
def aspis_core.field.PreparedQm31Multiplier.new
  (value : aspis_core.field.QM31) :
  Result aspis_core.field.PreparedQm31Multiplier
  := do
  let a ←
    aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () value.c0
  let a1 ←
    aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () value.c1
  let c ← aspis_core.field.CM31.add value.c0 value.c1
  let a2 ←
    aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () c
  ok { components := (Array.make 3#usize [ a, a1, a2 ]) }

/-- [aspis_core::field::mul_by_r]:
    Source: 'crates/aspis-core/src/field.rs', lines 860:0-860:28
    Name pattern: [aspis_core::field::mul_by_r] -/
@[rust_fun "aspis_core::field::mul_by_r"]
def aspis_core.field.mul_by_r
  (x : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let m ← aspis_core.field.M31.double x.a
  let m1 ← aspis_core.field.M31.sub m x.b
  let m2 ← aspis_core.field.M31.double x.b
  let m3 ← aspis_core.field.M31.add x.a m2
  ok { a := m1, b := m3 }

/-- [aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::mul::{impl core::ops::function::Fn<([aspis_core::field::M31; 3usize], aspis_core::field::CM31), aspis_core::field::CM31> for aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::mul::closure}::call]:
    Source: 'crates/aspis-core/src/field.rs', lines 461:23-461:52
    Name pattern: [aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::mul::{core::ops::function::Fn<aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::mul::closure, ([aspis_core::field::M31; 3], aspis_core::field::CM31), aspis_core::field::CM31>}::call] -/
@[rust_fun
  "aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::mul::{core::ops::function::Fn<aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::mul::closure, ([aspis_core::field::M31; 3], aspis_core::field::CM31), aspis_core::field::CM31>}::call"]
def
  aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
  (c : aspis_core.field.PreparedQm31Multiplier.mul.closure)
  (tupled_args : ((Array aspis_core.field.M31 3#usize) ×
  aspis_core.field.CM31)) :
  Result aspis_core.field.CM31
  := do
  let (left, right) := tupled_args
  let m ← Array.index_usize left 0#usize
  let m0 ← aspis_core.field.M31.mul m right.a
  let m1 ← Array.index_usize left 1#usize
  let m11 ← aspis_core.field.M31.mul m1 right.b
  let m2 ← Array.index_usize left 2#usize
  let m3 ← aspis_core.field.M31.add right.a right.b
  let m21 ← aspis_core.field.M31.mul m2 m3
  let m4 ← aspis_core.field.M31.sub m0 m11
  let m5 ← aspis_core.field.M31.sub m21 m0
  let m6 ← aspis_core.field.M31.sub m5 m11
  ok { a := m4, b := m6 }

/-- [aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 460:4-460:39
    Name pattern: [aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::mul]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{aspis_core::field::PreparedQm31Multiplier}::mul"]
def aspis_core.field.PreparedQm31Multiplier.mul
  (self : aspis_core.field.PreparedQm31Multiplier)
  (rhs : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let a ← Array.index_usize self.components 0#usize
  let m0 ←
    aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a, rhs.c0)
  let a1 ← Array.index_usize self.components 1#usize
  let m1 ←
    aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a1, rhs.c1)
  let a2 ← Array.index_usize self.components 2#usize
  let c ← aspis_core.field.CM31.add rhs.c0 rhs.c1
  let m2 ←
    aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a2, c)
  let c1 ← aspis_core.field.mul_by_r m1
  let c2 ← aspis_core.field.CM31.add m0 c1
  let c3 ← aspis_core.field.CM31.sub m2 m0
  let c4 ← aspis_core.field.CM31.sub c3 m1
  ok { c0 := c2, c1 := c4 }

/-- [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Source: 'crates/aspis-core/src/field.rs', lines 869:4-869:24
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::QM31}::ZERO"]
def aspis_core.field.QM31.ZERO : aspis_core.field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_core::field::{aspis_core::field::QM31}::ONE]
    Source: 'crates/aspis-core/src/field.rs', lines 879:4-879:23
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::ONE]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::QM31}::ONE"]
def aspis_core.field.QM31.ONE : aspis_core.field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_core::field::{aspis_core::field::QM31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 896:4-896:39
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::add]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::add"]
def aspis_core.field.QM31.add
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let c ← aspis_core.field.CM31.add self.c0 rhs.c0
  let c1 ← aspis_core.field.CM31.add self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_core::field::{aspis_core::field::QM31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 935:4-935:39
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::mul]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::mul"]
def aspis_core.field.QM31.mul
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let m0 ← aspis_core.field.CM31.mul self.c0 rhs.c0
  let m1 ← aspis_core.field.CM31.mul self.c1 rhs.c1
  let c ← aspis_core.field.CM31.add self.c0 self.c1
  let c1 ← aspis_core.field.CM31.add rhs.c0 rhs.c1
  let m2 ← aspis_core.field.CM31.mul c c1
  let c2 ← aspis_core.field.mul_by_r m1
  let c3 ← aspis_core.field.CM31.add m0 c2
  let c4 ← aspis_core.field.CM31.sub m2 m0
  let c5 ← aspis_core.field.CM31.sub c4 m1
  ok { c0 := c3, c1 := c5 }

/-- [aspis_core::field::{aspis_core::field::QM31}::square]:
    Source: 'crates/aspis-core/src/field.rs', lines 951:4-951:31
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::square]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::square"]
def aspis_core.field.QM31.square
  (self : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let c0_square ← aspis_core.field.CM31.square self.c0
  let c1_square ← aspis_core.field.CM31.square self.c1
  let c ← aspis_core.field.mul_by_r c1_square
  let c1 ← aspis_core.field.CM31.add c0_square c
  let c2 ← aspis_core.field.CM31.mul self.c0 self.c1
  let c3 ← aspis_core.field.CM31.double c2
  ok { c0 := c1, c1 := c3 }

/-- [aspis_core::field::{aspis_core::field::QM31}::mul_m31]:
    Source: 'crates/aspis-core/src/field.rs', lines 975:4-975:42
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::mul_m31]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::mul_m31"]
def aspis_core.field.QM31.mul_m31
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.QM31
  := do
  let c ← aspis_core.field.CM31.mul_m31 self.c0 rhs
  let c1 ← aspis_core.field.CM31.mul_m31 self.c1 rhs
  ok { c0 := c, c1 }

/-- [aspis_core::field::{aspis_core::field::M31}::neg]:
    Source: 'crates/aspis-core/src/field.rs', lines 3287:4-3287:28
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::neg]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::neg"]
def aspis_core.field.M31.neg
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  let i ← aspis_core.field.ct.neg self
  ok i


end R1Z.PV_RDCD3_FieldSource
