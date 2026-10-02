import Aeneas.Std
import AspisR156FullFreeze.FunsCore
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR156FullFreeze
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section
namespace AspisR249R110Raw

/-- Generated r110_norm private scalar representation, fixed to the pinned word API. -/
@[reducible] def circle_norm.joined_inverse.line_norm.r110_norm.B := Std.U32
/-- Generated r110_norm private pair representation. -/
def circle_norm.joined_inverse.line_norm.r110_norm.C :=
  circle_norm.joined_inverse.line_norm.r110_norm.B ×
  circle_norm.joined_inverse.line_norm.r110_norm.B

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::P110]
    Source: '../r110_norm.rs', lines 4:0-4:27 -/
@[global_simps, irreducible]
def circle_norm.joined_inverse.line_norm.r110_norm.P110 : Std.U32 :=
  2147483647#u32

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::input]:
    Source: '../r110_norm.rs', lines 8:4-8:73 -/
def circle_norm.joined_inverse.line_norm.r110_norm.B.input
  (x : aspis_core.field.M31) :
  Result (Option circle_norm.joined_inverse.line_norm.r110_norm.B)
  := do
  if x < circle_norm.joined_inverse.line_norm.r110_norm.P110
  then ok (some x)
  else ok none

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::reduce]:
    Source: '../r110_norm.rs', lines 9:21-9:71 -/
def circle_norm.joined_inverse.line_norm.r110_norm.B.reduce
  (x : Std.U64) : Result circle_norm.joined_inverse.line_norm.r110_norm.B := do
  let m ← aspis_core.field.M31.reduce_u64 x
  ok m

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::add]:
    Source: '../r110_norm.rs', lines 10:21-10:110 -/
def circle_norm.joined_inverse.line_norm.r110_norm.B.add
  (self : circle_norm.joined_inverse.line_norm.r110_norm.B)
  (r : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.B
  := do
  let x ← lift (Std.U32.wrapping_add self r)
  if x >= circle_norm.joined_inverse.line_norm.r110_norm.P110
  then
    let x1 ←
      lift (Std.U32.wrapping_sub x
        circle_norm.joined_inverse.line_norm.r110_norm.P110)
    ok x1
  else ok x

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::sub]:
    Source: '../r110_norm.rs', lines 11:21-11:129 -/
def circle_norm.joined_inverse.line_norm.r110_norm.B.sub
  (self : circle_norm.joined_inverse.line_norm.r110_norm.B)
  (r : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.B
  := do
  let i ←
    lift (Std.U32.wrapping_add self
      circle_norm.joined_inverse.line_norm.r110_norm.P110)
  let x ← lift (Std.U32.wrapping_sub i r)
  if x >= circle_norm.joined_inverse.line_norm.r110_norm.P110
  then
    let x1 ←
      lift (Std.U32.wrapping_sub x
        circle_norm.joined_inverse.line_norm.r110_norm.P110)
    ok x1
  else ok x

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::half]:
    Source: '../r110_norm.rs', lines 13:21-13:76 -/
def circle_norm.joined_inverse.line_norm.r110_norm.B.half
  (self : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.B
  := do
  let i ← lift (Std.U32.wrapping_shr self 1#u32)
  let i1 ← lift (self &&& 1#u32)
  let i2 ← lift (Std.U32.wrapping_shl i1 30#u32)
  let i3 ← lift (i ||| i2)
  ok i3

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::mul]:
    Source: '../r110_norm.rs', lines 14:21-19:5 -/
def circle_norm.joined_inverse.line_norm.r110_norm.B.mul
  (self : circle_norm.joined_inverse.line_norm.r110_norm.B)
  (r : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.B
  := do
  let i ← lift (core.convert.num.FromU64U32.from self)
  let i1 ← lift (core.convert.num.FromU64U32.from r)
  let x ← lift (Std.U64.wrapping_mul i i1)
  let i2 ←
    lift (core.convert.num.FromU64U32.from
      circle_norm.joined_inverse.line_norm.r110_norm.P110)
  let i3 ← lift (x &&& i2)
  let i4 ← lift (Std.U64.wrapping_shr x 31#u32)
  let s ← lift (Std.U64.wrapping_add i3 i4)
  let i5 ←
    lift (core.convert.num.FromU64U32.from
      circle_norm.joined_inverse.line_norm.r110_norm.P110)
  if s >= i5
  then
    let i6 ←
      lift (core.convert.num.FromU64U32.from
        circle_norm.joined_inverse.line_norm.r110_norm.P110)
    let i7 ← lift (Std.U64.wrapping_sub s i6)
    let i8 ← lift (UScalar.cast .U32 i7)
    ok i8
  else let i6 ← lift (UScalar.cast .U32 s)
       ok i6

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::output]:
    Source: '../r110_norm.rs', lines 25:4-25:65 -/
def circle_norm.joined_inverse.line_norm.r110_norm.C.output
  (self : circle_norm.joined_inverse.line_norm.r110_norm.C) :
  Result aspis_core.field.CM31
  := do
  let (b, b1) := self
  aspis_core.field.CM31.new b b1

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::add]:
    Source: '../r110_norm.rs', lines 26:21-26:85 -/
def circle_norm.joined_inverse.line_norm.r110_norm.C.add
  (self : circle_norm.joined_inverse.line_norm.r110_norm.C)
  (r : circle_norm.joined_inverse.line_norm.r110_norm.C) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.C
  := do
  let (b, b1) := self
  let (b2, b3) := r
  let b4 ← circle_norm.joined_inverse.line_norm.r110_norm.B.add b b2
  let b5 ← circle_norm.joined_inverse.line_norm.r110_norm.B.add b1 b3
  ok (b4, b5)

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::sub]:
    Source: '../r110_norm.rs', lines 27:21-27:85 -/
def circle_norm.joined_inverse.line_norm.r110_norm.C.sub
  (self : circle_norm.joined_inverse.line_norm.r110_norm.C)
  (r : circle_norm.joined_inverse.line_norm.r110_norm.C) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.C
  := do
  let (b, b1) := self
  let (b2, b3) := r
  let b4 ← circle_norm.joined_inverse.line_norm.r110_norm.B.sub b b2
  let b5 ← circle_norm.joined_inverse.line_norm.r110_norm.B.sub b1 b3
  ok (b4, b5)

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::half]:
    Source: '../r110_norm.rs', lines 29:21-29:75 -/
def circle_norm.joined_inverse.line_norm.r110_norm.C.half
  (self : circle_norm.joined_inverse.line_norm.r110_norm.C) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.C
  := do
  let (b, b1) := self
  let b2 ← circle_norm.joined_inverse.line_norm.r110_norm.B.half b
  let b3 ← circle_norm.joined_inverse.line_norm.r110_norm.B.half b1
  ok (b2, b3)

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::mul_m]:
    Source: '../r110_norm.rs', lines 30:21-30:80 -/
def circle_norm.joined_inverse.line_norm.r110_norm.C.mul_m
  (self : circle_norm.joined_inverse.line_norm.r110_norm.C)
  (r : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.C
  := do
  let (b, b1) := self
  let b2 ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul b r
  let b3 ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul b1 r
  ok (b2, b3)

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::mul::PP]
    Source: '../r110_norm.rs', lines 32:8-32:49 -/
@[global_simps, irreducible]
def circle_norm.joined_inverse.line_norm.r110_norm.C.mul.PP
  : Result Std.U64 := do
  let i ←
    lift (UScalar.cast .U64
      circle_norm.joined_inverse.line_norm.r110_norm.P110)
  let i1 ←
    lift (UScalar.cast .U64
      circle_norm.joined_inverse.line_norm.r110_norm.P110)
  i * i1

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::mul]:
    Source: '../r110_norm.rs', lines 31:21-36:5 -/
def circle_norm.joined_inverse.line_norm.r110_norm.C.mul
  (self : circle_norm.joined_inverse.line_norm.r110_norm.C)
  (r : circle_norm.joined_inverse.line_norm.r110_norm.C) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.C
  := do
  let (b, b1) := self
  let a ← lift (core.convert.num.FromU64U32.from b)
  let b2 ← lift (core.convert.num.FromU64U32.from b1)
  let (b3, b4) := r
  let c ← lift (core.convert.num.FromU64U32.from b3)
  let d ← lift (core.convert.num.FromU64U32.from b4)
  let i ← lift (Std.U64.wrapping_mul a c)
  let i1 ← circle_norm.joined_inverse.line_norm.r110_norm.C.mul.PP
  let i2 ← lift (Std.U64.wrapping_add i i1)
  let i3 ← lift (Std.U64.wrapping_mul b2 d)
  let i4 ← lift (Std.U64.wrapping_sub i2 i3)
  let b5 ← circle_norm.joined_inverse.line_norm.r110_norm.B.reduce i4
  let i5 ← lift (Std.U64.wrapping_mul a d)
  let i6 ← lift (Std.U64.wrapping_mul b2 c)
  let i7 ← lift (Std.U64.wrapping_add i5 i6)
  let b6 ← circle_norm.joined_inverse.line_norm.r110_norm.B.reduce i7
  ok (b5, b6)

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::square]:
    Source: '../r110_norm.rs', lines 37:21-40:5 -/
def circle_norm.joined_inverse.line_norm.r110_norm.C.square
  (self : circle_norm.joined_inverse.line_norm.r110_norm.C) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.C
  := do
  let (b, b1) := self
  let a ← lift (core.convert.num.FromU64U32.from b)
  let b2 ← lift (core.convert.num.FromU64U32.from b1)
  let i ← lift (Std.U64.wrapping_add a b2)
  let i1 ←
    lift (core.convert.num.FromU64U32.from
      circle_norm.joined_inverse.line_norm.r110_norm.P110)
  let i2 ← lift (Std.U64.wrapping_add a i1)
  let i3 ← lift (Std.U64.wrapping_sub i2 b2)
  let i4 ← lift (Std.U64.wrapping_mul i i3)
  let b3 ← circle_norm.joined_inverse.line_norm.r110_norm.B.reduce i4
  let b4 ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul b b1
  let b5 ← circle_norm.joined_inverse.line_norm.r110_norm.B.add b4 b4
  ok (b3, b5)

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::times_r]:
    Source: '../r110_norm.rs', lines 41:21-41:112 -/
def circle_norm.joined_inverse.line_norm.r110_norm.C.times_r
  (self : circle_norm.joined_inverse.line_norm.r110_norm.C) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.C
  := do
  let (b, b1) := self
  let b2 ← circle_norm.joined_inverse.line_norm.r110_norm.B.add b b
  let b3 ← circle_norm.joined_inverse.line_norm.r110_norm.B.sub b2 b1
  let b4 ← circle_norm.joined_inverse.line_norm.r110_norm.B.add b1 b1
  let b5 ← circle_norm.joined_inverse.line_norm.r110_norm.B.add b b4
  ok (b3, b5)

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::norm]:
    Source: '../r110_norm.rs', lines 42:21-42:109 -/
def circle_norm.joined_inverse.line_norm.r110_norm.C.norm
  (self : circle_norm.joined_inverse.line_norm.r110_norm.C) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.B
  := do
  let (b, b1) := self
  let a ← lift (core.convert.num.FromU64U32.from b)
  let b2 ← lift (core.convert.num.FromU64U32.from b1)
  let i ← lift (Std.U64.wrapping_mul a a)
  let i1 ← lift (Std.U64.wrapping_mul b2 b2)
  let i2 ← lift (Std.U64.wrapping_add i i1)
  circle_norm.joined_inverse.line_norm.r110_norm.B.reduce i2

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::double]:
    Source: '../r110_norm.rs', lines 28:21-28:58 -/
def circle_norm.joined_inverse.line_norm.r110_norm.C.double
  (self : circle_norm.joined_inverse.line_norm.r110_norm.C) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.C
  := do
  circle_norm.joined_inverse.line_norm.r110_norm.C.add self self

/-- Aeneas' generated nonnegative signed count 1 and the pinned unsigned count agree. -/
theorem count_one : (1#i32 : I32).bv.toNat = (1#u32 : U32).val := by decide
/-- Aeneas' generated nonnegative signed count 30 and the pinned unsigned count agree. -/
theorem count_thirty : (30#i32 : I32).bv.toNat = (30#u32 : U32).val := by decide
/-- Aeneas' generated nonnegative signed count 31 and the pinned unsigned count agree. -/
theorem count_thirty_one : (31#i32 : I32).bv.toNat = (31#u32 : U32).val := by decide

#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.P110
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.input
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.reduce
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.add
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.sub
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.half
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.mul
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.output
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.add
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.sub
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.half
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.mul_m
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.mul.PP
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.mul
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.square
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.times_r
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.norm
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.double
#print axioms count_one
#print axioms count_thirty
#print axioms count_thirty_one
end AspisR249R110Raw
end