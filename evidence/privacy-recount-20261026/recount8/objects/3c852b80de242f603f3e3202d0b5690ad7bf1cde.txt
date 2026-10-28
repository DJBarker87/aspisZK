import R1Z.ProverRwSuccessBorrow
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessInverseSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull ProverRwDictionaryTower
abbrev field.M31 := U32
abbrev field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev field.P := AspisR1ProducerRelease47.field.P
abbrev field.M31.ZERO := AspisR1ProducerRelease47.field.M31.ZERO
abbrev field.M31.ONE := AspisR1ProducerRelease47.field.M31.ONE
abbrev field.M31.mul := AspisR1ProducerRelease47.field.M31.mul
abbrev field.M31.add := AspisR1ProducerRelease47.field.M31.add
abbrev field.M31.neg := AspisR1ProducerRelease47.field.M31.neg
abbrev field.M31.Insts.CoreCmpPartialEqM31.eq := ProverRwDictionaryDerived.mEq
abbrev field.CM31.new := ProverRwDictionaryBytes.Src.complex

def field.CM31.mul (a b : C) : Result C := mapResult fromC
  (AspisR1ProducerRelease47.field.CM31.mul (toC a) (toC b))
def field.CM31.sub (a b : C) : Result C := mapResult fromC
  (AspisR1ProducerRelease47.field.CM31.sub (toC a) (toC b))
def field.CM31.neg (a : C) : Result C := mapResult fromC
  (AspisR1ProducerRelease47.field.CM31.neg (toC a))
def field.M31.pow_loop.body
  (exp : Std.U64) (base : field.M31) (acc : field.M31) :
  Result (ControlFlow (Std.U64 × field.M31 × field.M31) field.M31)
  := do
  if exp > 0#u64
  then
    let i ← lift (exp &&& 1#u64)
    let acc1 ← if i = 1#u64
                 then field.M31.mul acc base
                 else ok acc
    let base1 ← field.M31.mul base base
    let exp1 ← lift (Std.U64.wrapping_shr exp 1#u32)
    ok (cont (exp1, base1, acc1))
  else ok (done acc)

def field.M31.pow_loop
  (exp : Std.U64) (base : field.M31) (acc : field.M31) : Result field.M31 := do
  loop
    (fun (exp1, base1, acc1) => field.M31.pow_loop.body exp1 base1 acc1)
    (exp, base, acc)

def field.M31.pow (self : field.M31) (exp : Std.U64) : Result field.M31 := do
  field.M31.pow_loop exp self field.M31.ONE

def field.QM31.neg (self : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.neg self.c0
  let c1 ← field.CM31.neg self.c1
  ok { c0 := c, c1 }

def field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
  (self : field.M31) : Result (Option field.M31) := do
  let b ← field.M31.Insts.CoreCmpPartialEqM31.eq self field.M31.ZERO
  if b
  then ok none
  else
    let i ← lift (Std.U32.wrapping_sub field.P 2#u32)
    let i1 ← lift (core.convert.num.FromU64U32.from i)
    let m ← field.M31.pow self i1
    ok (some m)

def field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
  (self : field.CM31) : Result (Option field.CM31) := do
  let m ← field.M31.mul self.a self.a
  let m1 ← field.M31.mul self.b self.b
  let norm ← field.M31.add m m1
  let o ← field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv norm
  let cf ← ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let m2 ← field.M31.mul self.a val
    let m3 ← field.M31.neg self.b
    let m4 ← field.M31.mul m3 val
    ok (some { a := m2, b := m4 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      field.CM31 residual

def field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
  (self : field.QM31) : Result (Option field.QM31) := do
  let r ← field.CM31.new 2#u32 field.M31.ONE
  let c ← field.CM31.mul self.c0 self.c0
  let c1 ← field.CM31.mul self.c1 self.c1
  let c2 ← field.CM31.mul r c1
  let norm ← field.CM31.sub c c2
  let o ← field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv norm
  let cf ← ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let c3 ← field.CM31.mul self.c0 val
    let c4 ← field.CM31.neg self.c1
    let c5 ← field.CM31.mul c4 val
    ok (some { c0 := c3, c1 := c5 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      field.QM31 residual
end R1Z.ProverRwSuccessInverseSource
