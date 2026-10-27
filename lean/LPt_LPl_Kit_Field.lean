import Aeneas
import LPt_LPl_Kit_Types
open Aeneas Aeneas.Std Result ControlFlow Error
namespace LPt_LPl_Kit_Field
abbrev field.M31 := LPt_LPl_Kit_Release.aspis_core.field.M31
abbrev field.CM31 := LPt_LPl_Kit_Release.aspis_core.field.CM31
abbrev field.QM31 := LPt_LPl_Kit_Release.aspis_core.field.QM31
/- Definitions below reused from SOURCE (through mul_u), with namespace only.
 SOURCE: docs/research/100bit-spend-path-20261013/evidence/s9-wide-exact-mul-source-cut-v1-20261022/evidence/aeneas/generated/AspisR1S9ActualWideMulCutV1/Funs.lean
 Field source-to-release association remains separate from these definitions. -/
def field.P : U32 := 2147483647#u32
def field.M31.add (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let s ← lift (Std.U32.wrapping_add self rhs)
  if s >= field.P
  then let s1 ← lift (Std.U32.wrapping_sub s field.P)
       ok s1
  else ok s

/-- [s9_helper_actual_field_types_cut::field::{s9_helper_actual_field_types_cut::field::M31}::double]:
    Source: 'src/field.rs', lines 183:4-185:5
    Visibility: public -/
def field.M31.double (self : field.M31) : Result field.M31 := do
  field.M31.add self self

/-- [s9_helper_actual_field_types_cut::field::{s9_helper_actual_field_types_cut::field::M31}::sub]:
    Source: 'src/field.rs', lines 94:4-119:5
    Visibility: public -/
def field.M31.sub (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (Std.U32.wrapping_add self field.P)
  let s ← lift (Std.U32.wrapping_sub i rhs)
  if s >= field.P
  then let s1 ← lift (Std.U32.wrapping_sub s field.P)
       ok s1
  else ok s

/-- [s9_helper_actual_field_types_cut::field::mul_by_r]:
    Source: 'src/field.rs', lines 860:0-866:1 -/
def field.mul_by_r (x : field.CM31) : Result field.CM31 := do
  let m ← field.M31.double x.a
  let m1 ← field.M31.sub m x.b
  let m2 ← field.M31.double x.b
  let m3 ← field.M31.add x.a m2
  ok { a := m1, b := m3 }

/-- [s9_helper_actual_field_types_cut::field::reduce_u64]:
    Source: 'src/field.rs', lines 31:0-44:1 -/
def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← lift (Std.U64.wrapping_shr x 31#u32)
  let x1 ← lift (Std.U64.wrapping_add i1 i2)
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← lift (Std.U64.wrapping_shr x1 31#u32)
  let x2 ← lift (Std.U64.wrapping_add i4 i5)
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then ok (Std.U32.wrapping_sub x3 field.P)
  else ok x3

/-- [s9_helper_actual_field_types_cut::field::{s9_helper_actual_field_types_cut::field::M31}::reduce_u64]:
    Source: 'src/field.rs', lines 153:4-155:5
    Visibility: public -/
def field.M31.reduce_u64 (value : Std.U64) : Result field.M31 := do
  let i ← field.reduce_u64 value
  ok i

/-- [s9_helper_actual_field_types_cut::field::{s9_helper_actual_field_types_cut::field::M31}::mul]:
    Source: 'src/field.rs', lines 133:4-137:5
    Visibility: public -/
def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← lift (Std.U64.wrapping_mul i i1)
  let i3 ← field.reduce_u64 i2
  ok i3

/-- [s9_helper_actual_field_types_cut::field::{s9_helper_actual_field_types_cut::field::CM31}::mul]:
    Source: 'src/field.rs', lines 306:4-320:5
    Visibility: public -/
def field.CM31.mul
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m0 ← field.M31.mul self.a rhs.a
  let m1 ← field.M31.mul self.b rhs.b
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
  let m2 ← field.M31.reduce_u64 i10
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { a := m, b := m4 }

/-- [s9_helper_actual_field_types_cut::field::{s9_helper_actual_field_types_cut::field::CM31}::sub]:
    Source: 'src/field.rs', lines 289:4-294:5
    Visibility: public -/
def field.CM31.sub
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.sub self.a rhs.a
  let m1 ← field.M31.sub self.b rhs.b
  ok { a := m, b := m1 }

/-- [s9_helper_actual_field_types_cut::field::{s9_helper_actual_field_types_cut::field::CM31}::add]:
    Source: 'src/field.rs', lines 281:4-286:5
    Visibility: public -/
def field.CM31.add
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.add self.a rhs.a
  let m1 ← field.M31.add self.b rhs.b
  ok { a := m, b := m1 }

/-- [s9_helper_actual_field_types_cut::field::{s9_helper_actual_field_types_cut::field::QM31}::mul]:
    Source: 'src/field.rs', lines 935:4-945:5
    Visibility: public -/
def field.QM31.mul
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let m0 ← field.CM31.mul self.c0 rhs.c0
  let m1 ← field.CM31.mul self.c1 rhs.c1
  let c ← field.CM31.add self.c0 self.c1
  let c1 ← field.CM31.add rhs.c0 rhs.c1
  let m2 ← field.CM31.mul c c1
  let c2 ← field.mul_by_r m1
  let c3 ← field.CM31.add m0 c2
  let c4 ← field.CM31.sub m2 m0
  let c5 ← field.CM31.sub c4 m1
  ok { c0 := c3, c1 := c5 }

/-- [s9_helper_actual_field_types_cut::field::{s9_helper_actual_field_types_cut::field::QM31}::sub]:
    Source: 'src/field.rs', lines 906:4-913:5
    Visibility: public -/
def field.QM31.sub
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.sub self.c0 rhs.c0
  let c1 ← field.CM31.sub self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [s9_helper_actual_field_types_cut::field::{s9_helper_actual_field_types_cut::field::QM31}::add]:
    Source: 'src/field.rs', lines 896:4-903:5
    Visibility: public -/
def field.QM31.add
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.add self.c0 rhs.c0
  let c1 ← field.CM31.add self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [s9_helper_actual_field_types_cut::field::wide_exact::mul_u]:
    Source: 'src/field/wide_exact.rs', lines 299:0-304:1 -/
def field.wide_exact.mul_u (value : field.QM31) : Result field.QM31 := do
  let c ← field.mul_by_r value.c1
  ok { c0 := c, c1 := value.c0 }


end LPt_LPl_Kit_Field
