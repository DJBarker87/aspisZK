import RPu_FIq_NativeExternal
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- Trait implementation: [core::array::iter::{impl core::iter::traits::iterator::Iterator<T> for core::array::iter::IntoIter<T, N>}]
    Source: '/rustc/library/core/src/array/iter.rs', lines 238:0-238:51
    Name pattern: [core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>"]
impl_def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator (T :
  Type) (N : Std.Usize) : core.iter.traits.iterator.Iterator
  (core.array.iter.IntoIter T N) T := {
  next := core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N)

}

/-- Trait implementation: [core::array::iter::{impl core::iter::traits::double_ended::DoubleEndedIterator<T> for core::array::iter::IntoIter<T, N>}]
    Source: '/rustc/library/core/src/array/iter.rs', lines 295:0-295:62
    Name pattern: [core::iter::traits::double_ended::DoubleEndedIterator<core::array::iter::IntoIter<@T, @N>, @T>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::double_ended::DoubleEndedIterator<core::array::iter::IntoIter<@T, @N>, @T>"]
def
  core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
  (T : Type) (N : Std.Usize) :
  core.iter.traits.double_ended.DoubleEndedIterator (core.array.iter.IntoIter T
  N) T := {
  iteratorInst := core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
    T N
  next_back :=
    core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back
}

/-- Trait implementation: [core::option::{impl core::cmp::PartialEq<core::option::Option<T>> for core::option::Option<T>}]
    Source: '/rustc/library/core/src/option.rs', lines 2438:0-2438:56
    Name pattern: [core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>] -/
@[reducible, rust_trait_impl
  "core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>"]
impl_def core.option.Option.Insts.CoreCmpPartialEqOption {T : Type}
  (cmpPartialEqInst : core.cmp.PartialEq T T) : core.cmp.PartialEq (Option T)
  (Option T) := {
  eq := core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst
  ne := core.cmp.PartialEq.ne.trait_default
    (core.option.Option.Insts.CoreCmpPartialEqOption cmpPartialEqInst)
}

/-- Trait implementation: [core::slice::iter::{impl core::iter::traits::double_ended::DoubleEndedIterator<&'_ T> for core::slice::iter::Iter<'a, T>}]
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 436:8-436:56
    Name pattern: [core::iter::traits::double_ended::DoubleEndedIterator<core::slice::iter::Iter<'a, @T>, &'_ @T>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::double_ended::DoubleEndedIterator<core::slice::iter::Iter<'a, @T>, &'_ @T>"]
def
  core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
  (T : Type) : core.iter.traits.double_ended.DoubleEndedIterator
  (core.slice.iter.Iter T) T := {
  iteratorInst := core.iter.traits.iterator.IteratorSliceIter T
  next_back :=
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back
}

/-- [aspis_r1_mask_extraction_probe::field::P]
    Source: 'src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_r1_mask_extraction_probe::field::{impl core::cmp::PartialEq<aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::field::M31}::eq]:
    Source: 'src/field.rs', lines 22:22-22:31
    Visibility: public -/
def field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : field.M31) (other : field.M31) : Result Bool := do
  ok (self = other)

/-- Trait implementation: [aspis_r1_mask_extraction_probe::field::{impl core::cmp::PartialEq<aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::field::M31}]
    Source: 'src/field.rs', lines 22:22-22:31 -/
@[reducible]
impl_def field.M31.Insts.CoreCmpPartialEqM31 : core.cmp.PartialEq field.M31
  field.M31 := {
  eq := field.M31.Insts.CoreCmpPartialEqM31.eq
  ne := core.cmp.PartialEq.ne.trait_default field.M31.Insts.CoreCmpPartialEqM31
}

/-- [aspis_r1_mask_extraction_probe::field::M31]:
    Source: 'src/field.rs', lines 23:0-23:24 -/
def field.M31_constructor (i : Std.U32) : Result field.M31 := do
  ok i

/-- [aspis_r1_mask_extraction_probe::field::reduce_u64]:
    Source: 'src/field.rs', lines 31:0-44:1 -/
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

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::M31}::ZERO]
    Source: 'src/field.rs', lines 55:4-55:33
    Visibility: public -/
@[global_simps, irreducible] def field.M31.ZERO : field.M31 := 0#u32

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::M31}::ONE]
    Source: 'src/field.rs', lines 56:4-56:32
    Visibility: public -/
@[global_simps, irreducible] def field.M31.ONE : field.M31 := 1#u32

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::M31}::add]:
    Source: 'src/field.rs', lines 62:4-88:5
    Visibility: public -/
def field.M31.add (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let s ← self + rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::M31}::sub]:
    Source: 'src/field.rs', lines 94:4-119:5
    Visibility: public -/
def field.M31.sub (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← self + field.P
  let s ← i - rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::M31}::mul]:
    Source: 'src/field.rs', lines 133:4-137:5
    Visibility: public -/
def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← field.reduce_u64 i2
  ok i3

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::M31}::reduce_u62]:
    Source: 'src/field.rs', lines 145:4-148:5
    Visibility: public -/
def field.M31.reduce_u62 (value : Std.U64) : Result field.M31 := do
  let i ← field.reduce_u64 value
  ok i

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::M31}::reduce_u64]:
    Source: 'src/field.rs', lines 153:4-155:5
    Visibility: public -/
def field.M31.reduce_u64 (value : Std.U64) : Result field.M31 := do
  let i ← field.reduce_u64 value
  ok i

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::M31}::double]:
    Source: 'src/field.rs', lines 183:4-185:5
    Visibility: public -/
def field.M31.double (self : field.M31) : Result field.M31 := do
  field.M31.add self self

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::CM31}::ZERO]
    Source: 'src/field.rs', lines 261:4-264:6
    Visibility: public -/
@[global_simps, irreducible]
def field.CM31.ZERO : field.CM31 := { a := 0#u32, b := 0#u32 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::CM31}::new]:
    Source: 'src/field.rs', lines 271:4-273:5
    Visibility: public -/
def field.CM31.new (a : field.M31) (b : field.M31) : Result field.CM31 := do
  ok { a, b }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::CM31}::from_m31]:
    Source: 'src/field.rs', lines 276:4-278:5
    Visibility: public -/
def field.CM31.from_m31 (a : field.M31) : Result field.CM31 := do
  ok { a, b := field.M31.ZERO }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::CM31}::add]:
    Source: 'src/field.rs', lines 281:4-286:5
    Visibility: public -/
def field.CM31.add
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.add self.a rhs.a
  let m1 ← field.M31.add self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::CM31}::sub]:
    Source: 'src/field.rs', lines 289:4-294:5
    Visibility: public -/
def field.CM31.sub
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.sub self.a rhs.a
  let m1 ← field.M31.sub self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::CM31}::mul]:
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
  let i4 ← i1 + i3
  let i5 := rhs.a
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← i6 + i8
  let i10 ← i4 * i9
  let m2 ← field.M31.reduce_u64 i10
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { a := m, b := m4 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::CM31}::square]:
    Source: 'src/field.rs', lines 325:4-335:5
    Visibility: public -/
def field.CM31.square (self : field.CM31) : Result field.CM31 := do
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 ← lift (core.convert.num.FromU64U32.from i)
  let i6 ← lift (core.convert.num.FromU64U32.from field.P)
  let i7 ← i5 + i6
  let i8 ← lift (core.convert.num.FromU64U32.from i2)
  let i9 ← i7 - i8
  let i10 ← i4 * i9
  let m ← field.M31.reduce_u64 i10
  let m1 ← field.M31.mul self.a self.b
  let m2 ← field.M31.double m1
  ok { a := m, b := m2 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::CM31}::mul_m31]:
    Source: 'src/field.rs', lines 338:4-343:5
    Visibility: public -/
def field.CM31.mul_m31
  (self : field.CM31) (rhs : field.M31) : Result field.CM31 := do
  let m ← field.M31.mul self.a rhs
  let m1 ← field.M31.mul self.b rhs
  ok { a := m, b := m1 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::CM31}::double]:
    Source: 'src/field.rs', lines 346:4-348:5
    Visibility: public -/
def field.CM31.double (self : field.CM31) : Result field.CM31 := do
  field.CM31.add self self

/-- [aspis_r1_mask_extraction_probe::field::{impl core::clone::Clone for aspis_r1_mask_extraction_probe::field::QM31}::clone]:
    Source: 'src/field.rs', lines 431:9-431:14
    Visibility: public -/
def field.QM31.Insts.CoreCloneClone.clone
  (self : field.QM31) : Result field.QM31 := do
  ok self

/-- Trait implementation: [aspis_r1_mask_extraction_probe::field::{impl core::clone::Clone for aspis_r1_mask_extraction_probe::field::QM31}]
    Source: 'src/field.rs', lines 431:9-431:14 -/
@[reducible]
def field.QM31.Insts.CoreCloneClone : core.clone.Clone field.QM31 := {
  clone := field.QM31.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::field::{impl core::marker::Copy for aspis_r1_mask_extraction_probe::field::QM31}]
    Source: 'src/field.rs', lines 431:16-431:20 -/
@[reducible]
def field.QM31.Insts.CoreMarkerCopy : core.marker.Copy field.QM31 := {
  cloneInst := field.QM31.Insts.CoreCloneClone
}

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::new::{impl core::ops::function::Fn<(aspis_r1_mask_extraction_probe::field::CM31,), [aspis_r1_mask_extraction_probe::field::M31; 3usize]> for aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::new::closure}::call]:
    Source: 'src/field.rs', lines 449:22-449:96 -/
def
  field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
  (c : field.PreparedQm31Multiplier.new.closure) (tupled_args : field.CM31) :
  Result (Array field.M31 3#usize)
  := do
  let m ← field.M31.add tupled_args.a tupled_args.b
  ok (Array.make 3#usize [ tupled_args.a, tupled_args.b, m ])

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::new]:
    Source: 'src/field.rs', lines 448:4-457:5
    Visibility: public -/
def field.PreparedQm31Multiplier.new
  (value : field.QM31) : Result field.PreparedQm31Multiplier := do
  let a ←
    field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () value.c0
  let a1 ←
    field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () value.c1
  let c ← field.CM31.add value.c0 value.c1
  let a2 ←
    field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () c
  ok { components := (Array.make 3#usize [ a, a1, a2 ]) }

/-- [aspis_r1_mask_extraction_probe::field::mul_by_r]:
    Source: 'src/field.rs', lines 860:0-866:1 -/
def field.mul_by_r (x : field.CM31) : Result field.CM31 := do
  let m ← field.M31.double x.a
  let m1 ← field.M31.sub m x.b
  let m2 ← field.M31.double x.b
  let m3 ← field.M31.add x.a m2
  ok { a := m1, b := m3 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::mul::{impl core::ops::function::Fn<([aspis_r1_mask_extraction_probe::field::M31; 3usize], aspis_r1_mask_extraction_probe::field::CM31), aspis_r1_mask_extraction_probe::field::CM31> for aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::mul::closure}::call]:
    Source: 'src/field.rs', lines 461:23-469:9 -/
def
  field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
  (c : field.PreparedQm31Multiplier.mul.closure)
  (tupled_args : ((Array field.M31 3#usize) × field.CM31)) :
  Result field.CM31
  := do
  let (left, right) := tupled_args
  let m ← Array.index_usize left 0#usize
  let m0 ← field.M31.mul m right.a
  let m1 ← Array.index_usize left 1#usize
  let m11 ← field.M31.mul m1 right.b
  let m2 ← Array.index_usize left 2#usize
  let m3 ← field.M31.add right.a right.b
  let m21 ← field.M31.mul m2 m3
  let m4 ← field.M31.sub m0 m11
  let m5 ← field.M31.sub m21 m0
  let m6 ← field.M31.sub m5 m11
  ok { a := m4, b := m6 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::PreparedQm31Multiplier}::mul]:
    Source: 'src/field.rs', lines 460:4-477:5
    Visibility: public -/
def field.PreparedQm31Multiplier.mul
  (self : field.PreparedQm31Multiplier) (rhs : field.QM31) :
  Result field.QM31
  := do
  let a ← Array.index_usize self.components 0#usize
  let m0 ←
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a, rhs.c0)
  let a1 ← Array.index_usize self.components 1#usize
  let m1 ←
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a1, rhs.c1)
  let a2 ← Array.index_usize self.components 2#usize
  let c ← field.CM31.add rhs.c0 rhs.c1
  let m2 ←
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a2, c)
  let c1 ← field.mul_by_r m1
  let c2 ← field.CM31.add m0 c1
  let c3 ← field.CM31.sub m2 m0
  let c4 ← field.CM31.sub c3 m1
  ok { c0 := c2, c1 := c4 }

/-- [aspis_r1_mask_extraction_probe::field::qm31_from_karatsuba_channel_sums::{impl core::ops::function::Fn<([u64; 3usize],), aspis_r1_mask_extraction_probe::field::CM31> for aspis_r1_mask_extraction_probe::field::qm31_from_karatsuba_channel_sums::closure}::call]:
    Source: 'src/field.rs', lines 482:22-490:5 -/
def
  field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
  (c : field.qm31_from_karatsuba_channel_sums.closure)
  (tupled_args : Array Std.U64 3#usize) :
  Result field.CM31
  := do
  let i ← Array.index_usize tupled_args 0#usize
  let m0 ← field.M31.reduce_u64 i
  let i1 ← Array.index_usize tupled_args 1#usize
  let m1 ← field.M31.reduce_u64 i1
  let i2 ← Array.index_usize tupled_args 2#usize
  let m2 ← field.M31.reduce_u64 i2
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { a := m, b := m4 }

/-- [aspis_r1_mask_extraction_probe::field::qm31_from_karatsuba_channel_sums]:
    Source: 'src/field.rs', lines 481:0-498:1 -/
def field.qm31_from_karatsuba_channel_sums
  (sums : Array (Array Std.U64 3#usize) 3#usize) : Result field.QM31 := do
  let a ← Array.index_usize sums 0#usize
  let m0 ←
    field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
      () a
  let a1 ← Array.index_usize sums 1#usize
  let m1 ←
    field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
      () a1
  let a2 ← Array.index_usize sums 2#usize
  let m2 ←
    field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
      () a2
  let c ← field.mul_by_r m1
  let c1 ← field.CM31.add m0 c
  let c2 ← field.CM31.sub m2 m0
  let c3 ← field.CM31.sub c2 m1
  ok { c0 := c1, c1 := c3 }

/-- [aspis_r1_mask_extraction_probe::field::qm31_sum_products3_prepared]: loop 2:
    Source: 'src/field.rs', lines 696:12-699:13
    Visibility: public -/
@[rust_loop]
def field.qm31_sum_products3_prepared_loop0_loop0_loop0
  (iter : core.ops.range.Range Std.Usize)
  (left : Array field.PreparedQm31Multiplier 3#usize)
  (sums : Array (Array Std.U64 3#usize) 3#usize) (index : Std.Usize)
  (right_components : Array (Array field.M31 3#usize) 3#usize)
  (component : Std.Usize) :
  Result (Array (Array Std.U64 3#usize) 3#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok sums
  | some channel =>
    let pqm ← Array.index_usize left index
    let a ← Array.index_usize pqm.components component
    let m ← Array.index_usize a channel
    let i ← lift (UScalar.cast .U64 m)
    let a1 ← Array.index_usize right_components component
    let m1 ← Array.index_usize a1 channel
    let i1 ← lift (UScalar.cast .U64 m1)
    let i2 ← i * i1
    let a2 ← Array.index_usize sums component
    let i3 ← Array.index_usize a2 channel
    let i4 ← i3 + i2
    let (a3, index_mut_back) ← Array.index_mut_usize sums component
    let a4 ← Array.update a3 channel i4
    let a5 := index_mut_back a4
    field.qm31_sum_products3_prepared_loop0_loop0_loop0 iter1 left a5 index
      right_components component
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::field::qm31_sum_products3_prepared]: loop 1:
    Source: 'src/field.rs', lines 695:8-700:9
    Visibility: public -/
@[rust_loop]
def field.qm31_sum_products3_prepared_loop0_loop0
  (iter : core.ops.range.Range Std.Usize)
  (left : Array field.PreparedQm31Multiplier 3#usize)
  (sums : Array (Array Std.U64 3#usize) 3#usize) (index : Std.Usize)
  (right_components : Array (Array field.M31 3#usize) 3#usize) :
  Result (Array (Array Std.U64 3#usize) 3#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok sums
  | some component =>
    let sums1 ←
      field.qm31_sum_products3_prepared_loop0_loop0_loop0
        { start := 0#usize, «end» := 3#usize } left sums index
        right_components component
    field.qm31_sum_products3_prepared_loop0_loop0 iter1 left sums1 index
      right_components
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::field::qm31_sum_products3_prepared]: loop 0:
    Source: 'src/field.rs', lines 680:4-701:5
    Visibility: public -/
@[rust_loop]
def field.qm31_sum_products3_prepared_loop0
  (iter : core.ops.range.Range Std.Usize)
  (left : Array field.PreparedQm31Multiplier 3#usize)
  (right : Array field.QM31 3#usize)
  (sums : Array (Array Std.U64 3#usize) 3#usize) :
  Result (Array (Array Std.U64 3#usize) 3#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok sums
  | some index =>
    let q ← Array.index_usize right index
    let right_sum ← field.CM31.add q.c0 q.c1
    let m ← field.M31.add q.c0.a q.c0.b
    let m1 ← field.M31.add q.c1.a q.c1.b
    let m2 ← field.M31.add right_sum.a right_sum.b
    let sums1 ←
      field.qm31_sum_products3_prepared_loop0_loop0
        { start := 0#usize, «end» := 3#usize } left sums index
        (Array.make 3#usize [
          Array.make 3#usize [ q.c0.a, q.c0.b, m ],
          Array.make 3#usize [ q.c1.a, q.c1.b, m1 ],
          Array.make 3#usize [ right_sum.a, right_sum.b, m2 ]
          ])
    field.qm31_sum_products3_prepared_loop0 iter1 left right sums1
partial_fixpoint


end FIq_Native
