import R1Z.ProverRwSuccessErrorInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessNativePorts
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev aspis_core.field.wide_exact.WideExact := ProverRwFull.aspis_core.field.wide_exact.WideExact
abbrev aspis_core.field.wide_exact.canonical_qm31.closure := Unit
abbrev aspis_core.field.P : Result U32 := .ok AspisR1ProducerRelease47.field.P
abbrev aspis_core.field.M31.ZERO : Result U32 := .ok 0#u32
abbrev aspis_core.field.M31.ONE : Result U32 := .ok 1#u32
abbrev aspis_core.field.CM31.ZERO : Result aspis_core.field.CM31 := .ok ⟨0#u32,0#u32⟩
abbrev aspis_core.field.CM31.ONE : Result aspis_core.field.CM31 := .ok ⟨1#u32,0#u32⟩
abbrev aspis_core.field.M31.mul := AspisR1ProducerRelease47.field.M31.mul
abbrev aspis_core.field.M31.add := AspisR1ProducerRelease47.field.M31.add
abbrev aspis_core.field.M31.neg := AspisR1ProducerRelease47.field.M31.neg
abbrev aspis_core.field.M31.pow := ProverRwSuccessInverseSource.field.M31.pow
abbrev aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq := ProverRwDictionaryDerived.mEq
abbrev aspis_core.field.CM31.new := ProverRwDictionaryBytes.Src.complex
abbrev aspis_core.field.CM31.mul := ProverRwSuccessInverseSource.field.CM31.mul
abbrev aspis_core.field.CM31.sub := ProverRwSuccessInverseSource.field.CM31.sub
abbrev aspis_core.field.CM31.neg := ProverRwSuccessInverseSource.field.CM31.neg
abbrev aspis_core.field.QM31.mul := ProverRwDictionaryTower.qMul
abbrev aspis_core.field.QM31.sub := ProverRwDictionaryTower.qSub
abbrev aspis_core.field.QM31.neg := ProverRwSuccessInverseInstall.Src.qNeg
def aspis_core.field.ct.subtract_p (x : Std.U32) : Result Std.U32 := do
  let i ← aspis_core.field.P
  let i1 ← lift (UScalar.cast_fromBool .U32 (x >= i))
  let mask ← lift (core.num.U32.wrapping_sub 0#u32 i1)
  let i2 ← lift (i &&& mask)
  ok (core.num.U32.wrapping_sub x i2)

def aspis_core.field.ct.reduce64 (x : Std.U64) : Result Std.U32 := do
  let i ← aspis_core.field.P
  let i1 ← lift (UScalar.cast .U64 i)
  let i2 ← lift (x &&& i1)
  let i3 ← lift (Std.U64.wrapping_shr x 31#u32)
  let x1 ← lift (Std.U64.wrapping_add i2 i3)
  let i4 ← lift (UScalar.cast .U64 i)
  let i5 ← lift (x1 &&& i4)
  let i6 ← lift (Std.U64.wrapping_shr x1 31#u32)
  let x2 ← lift (Std.U64.wrapping_add i5 i6)
  let i7 ← lift (UScalar.cast .U32 x2)
  aspis_core.field.ct.subtract_p i7

def aspis_core.field.wide_exact.WideExact.U
  : Result aspis_core.field.QM31 := do
  let c ← aspis_core.field.CM31.ZERO
  let c1 ← aspis_core.field.CM31.ONE
  ok { c0 := c, c1 }

def
  aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
  (c : aspis_core.field.wide_exact.canonical_qm31.closure)
  (tupled_args : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← lift (UScalar.cast .U64 tupled_args)
  let i1 ← aspis_core.field.ct.reduce64 i
  ok i1

def aspis_core.field.wide_exact.canonical_qm31
  (value : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let m ←
    aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
      () value.c0.a
  let m1 ←
    aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
      () value.c0.b
  let m2 ←
    aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
      () value.c1.a
  let m3 ←
    aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
      () value.c1.b
  ok { c0 := { a := m, b := m1 }, c1 := { a := m2, b := m3 } }

def aspis_core.field.wide_exact.WideExact.new
  (c0 : aspis_core.field.QM31) (c1 : aspis_core.field.QM31) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let q ← aspis_core.field.wide_exact.canonical_qm31 c0
  let q1 ← aspis_core.field.wide_exact.canonical_qm31 c1
  ok { c0 := q, c1 := q1 }

def aspis_core.field.wide_exact.WideExact.impl.c0
  (self : aspis_core.field.wide_exact.WideExact) :
  Result aspis_core.field.QM31
  := do
  ok self.c0

def aspis_core.field.wide_exact.WideExact.impl.c1
  (self : aspis_core.field.wide_exact.WideExact) :
  Result aspis_core.field.QM31
  := do
  ok self.c1

def aspis_core.field.wide_exact.WideExact.neg
  (self : aspis_core.field.wide_exact.WideExact) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let q ← aspis_core.field.QM31.neg self.c0
  let q1 ← aspis_core.field.QM31.neg self.c1
  ok { c0 := q, c1 := q1 }

def aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg
  (self : aspis_core.field.wide_exact.WideExact) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  aspis_core.field.wide_exact.WideExact.neg self

def aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv
  (self : aspis_core.field.M31) : Result (Option aspis_core.field.M31) := do
  let m ← aspis_core.field.M31.ZERO
  let b ← aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq self m
  if b
  then ok none
  else
    let i ← aspis_core.field.P
    let i1 ← lift (Std.U32.wrapping_sub i 2#u32)
    let i2 ← lift (core.convert.num.FromU64U32.from i1)
    let m1 ← aspis_core.field.M31.pow self i2
    ok (some m1)

def aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.try_inv
  (self : aspis_core.field.CM31) : Result (Option aspis_core.field.CM31) := do
  let m ← aspis_core.field.M31.mul self.a self.a
  let m1 ← aspis_core.field.M31.mul self.b self.b
  let norm ← aspis_core.field.M31.add m m1
  let o ← aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv norm
  let cf ← ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let m2 ← aspis_core.field.M31.mul self.a val
    let m3 ← aspis_core.field.M31.neg self.b
    let m4 ← aspis_core.field.M31.mul m3 val
    ok (some { a := m2, b := m4 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      aspis_core.field.CM31 residual

def aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv
  (self : aspis_core.field.QM31) : Result (Option aspis_core.field.QM31) := do
  let m ← aspis_core.field.M31.ONE
  let r ← aspis_core.field.CM31.new 2#u32 m
  let c ← aspis_core.field.CM31.mul self.c0 self.c0
  let c1 ← aspis_core.field.CM31.mul self.c1 self.c1
  let c2 ← aspis_core.field.CM31.mul r c1
  let norm ← aspis_core.field.CM31.sub c c2
  let o ←
    aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.try_inv norm
  let cf ← ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let c3 ← aspis_core.field.CM31.mul self.c0 val
    let c4 ← aspis_core.field.CM31.neg self.c1
    let c5 ← aspis_core.field.CM31.mul c4 val
    ok (some { c0 := c3, c1 := c5 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      aspis_core.field.QM31 residual

def
  aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv
  (self : aspis_core.field.wide_exact.WideExact) :
  Result (Option aspis_core.field.wide_exact.WideExact)
  := do
  let q ← aspis_core.field.wide_exact.WideExact.impl.c0 self
  let q1 ← aspis_core.field.QM31.mul q q
  let q2 ← aspis_core.field.wide_exact.WideExact.impl.c1 self
  let q3 ← aspis_core.field.QM31.mul q2 q2
  let q4 ← aspis_core.field.wide_exact.WideExact.U
  let q5 ← aspis_core.field.QM31.mul q4 q3
  let norm ← aspis_core.field.QM31.sub q1 q5
  let o ←
    aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv norm
  let cf ← ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let q6 ← aspis_core.field.QM31.mul q val
    let q7 ← aspis_core.field.QM31.neg q2
    let q8 ← aspis_core.field.QM31.mul q7 val
    let we ← aspis_core.field.wide_exact.WideExact.new q6 q8
    ok (some we)
  | core.ops.control_flow.ControlFlow.Break residual =>
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      aspis_core.field.wide_exact.WideExact residual

def wide_neg
  (x : aspis_core.field.wide_exact.WideExact) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg x

def wide_inv
  (x : aspis_core.field.wide_exact.WideExact) :
  Result (Option aspis_core.field.wide_exact.WideExact)
  := do
  aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv
    x
end R1Z.ProverRwSuccessNativePorts
