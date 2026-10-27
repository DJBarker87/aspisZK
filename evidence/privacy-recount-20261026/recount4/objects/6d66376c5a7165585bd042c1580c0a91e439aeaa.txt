import R1Z.ProverRwP7ReverseSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7FibreSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
abbrev core.num.U32.reverse_bits := ProverRwP7ReverseSource.reverse32
abbrev aspis_core.field.P : Result U32 := .ok 2147483647#u32
abbrev aspis_core.field.M31.reduce_u64 := ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64
abbrev aspis_core.field.M31.mul := AspisR1ProducerRelease47.field.M31.mul
abbrev aspis_core.field.M31.double := AspisR1ProducerRelease47.field.M31.double
abbrev aspis_core.field.CM31.mul := ProverRwSuccessInverseSource.field.CM31.mul
/-- [aspis_core::field::{aspis_core::field::CM31}::ONE]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-core/src/field.rs', lines 265:4-265:23
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::ONE]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::CM31}::ONE"]
def aspis_core.field.CM31.ONE : aspis_core.field.CM31 :=
  { a := 1#u32, b := 0#u32 }

/-- [aspis_core::field::{aspis_core::field::CM31}::new]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-core/src/field.rs', lines 271:4-271:38
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::new]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::new"]
def aspis_core.field.CM31.new
  (a : aspis_core.field.M31) (b : aspis_core.field.M31) :
  Result aspis_core.field.CM31
  := do
  ok { a, b }

/-- [aspis_core::field::{aspis_core::field::CM31}::square]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-core/src/field.rs', lines 325:4-325:31
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
  let i6 ← aspis_core.field.P
  let i7 ← lift (core.convert.num.FromU64U32.from i6)
  let i8 ← lift (Std.U64.wrapping_add i5 i7)
  let i9 ← lift (core.convert.num.FromU64U32.from i2)
  let i10 ← lift (Std.U64.wrapping_sub i8 i9)
  let i11 ← lift (Std.U64.wrapping_mul i4 i10)
  let m ← aspis_core.field.M31.reduce_u64 i11
  let m1 ← aspis_core.field.M31.mul self.a self.b
  let m2 ← aspis_core.field.M31.double m1
  ok { a := m, b := m2 }

/-- [aspis_core::field::{aspis_core::field::CM31}::pow]: loop body 0:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-core/src/field.rs', lines 379:8-385:9
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::pow]
    Visibility: public -/
@[rust_loop_body, rust_fun "aspis_core::field::{aspis_core::field::CM31}::pow"]
def aspis_core.field.CM31.pow_loop.body
  (exp : Std.U64) (base : aspis_core.field.CM31) (acc : aspis_core.field.CM31)
  :
  Result (ControlFlow (Std.U64 × aspis_core.field.CM31 ×
    aspis_core.field.CM31) aspis_core.field.CM31)
  := do
  if exp > 0#u64
  then
    let i ← lift (exp &&& 1#u64)
    let acc1 ←
      if i = 1#u64
      then aspis_core.field.CM31.mul acc base
      else ok acc
    let base1 ← aspis_core.field.CM31.square base
    let exp1 ← lift (Std.U64.wrapping_shr exp 1#u32)
    ok (cont (exp1, base1, acc1))
  else ok (done acc)

/-- [aspis_core::field::{aspis_core::field::CM31}::pow]: loop 0:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-core/src/field.rs', lines 379:8-385:9
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::pow]
    Visibility: public -/
@[rust_loop, rust_fun "aspis_core::field::{aspis_core::field::CM31}::pow"]
def aspis_core.field.CM31.pow_loop
  (exp : Std.U64) (base : aspis_core.field.CM31) (acc : aspis_core.field.CM31)
  :
  Result aspis_core.field.CM31
  := do
  loop
    (fun (exp1, base1, acc1) => aspis_core.field.CM31.pow_loop.body exp1 base1
      acc1)
    (exp, base, acc)

/-- [aspis_core::field::{aspis_core::field::CM31}::pow]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-core/src/field.rs', lines 376:4-376:42
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::pow]
    Visibility: public -/
@[reducible, rust_fun "aspis_core::field::{aspis_core::field::CM31}::pow"]
def aspis_core.field.CM31.pow
  (self : aspis_core.field.CM31) (exp : Std.U64) :
  Result aspis_core.field.CM31
  := do
  aspis_core.field.CM31.pow_loop exp self aspis_core.field.CM31.ONE

/-- [aspis_core::r0::domain::rev18]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-core/src/r0/domain.rs', lines 52:0-52:36
    Name pattern: [aspis_core::r0::domain::rev18]
    Visibility: public -/
@[rust_fun "aspis_core::r0::domain::rev18"]
def aspis_core.r0.domain.rev18
  (u : aspis_core.r0.domain.FibreIndex) : Result Std.Usize := do
  let i ← lift (UScalar.cast .U32 u)
  let i1 ← core.num.U32.reverse_bits i
  let i2 ← lift (UScalar.cast .Usize i1)
  ok (Std.Usize.wrapping_shr i2 14#u32)

/-- [aspis_core::r0::domain::fibre_point]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-core/src/r0/domain.rs', lines 68:0-68:59
    Name pattern: [aspis_core::r0::domain::fibre_point]
    Visibility: public -/
@[rust_fun "aspis_core::r0::domain::fibre_point"]
def aspis_core.r0.domain.fibre_point
  {E : Type} (scalarCodeFieldInst : aspis_core.r0.scalar.CodeField E)
  (u : aspis_core.r0.domain.FibreIndex) :
  Result (aspis_core.r0.domain.Point E)
  := do
  let g ← aspis_core.field.CM31.new 2#u32 1268011823#u32
  let i ← aspis_core.r0.domain.rev18 u
  let i1 ← lift (UScalar.cast .U64 i)
  let i2 ← lift (Std.U64.wrapping_mul 4096#u64 i1)
  let i3 ← lift (Std.U64.wrapping_add 1024#u64 i2)
  let value ← aspis_core.field.CM31.pow g i3
  let t ← scalarCodeFieldInst.from_m31 value.a
  let t1 ← scalarCodeFieldInst.from_m31 value.b
  ok { x := t, y := t1 }

/-- [prover_rw_success_direct::fibre]:
    Source: 'lib.rs', lines 3:0-3:92
    Visibility: public -/
def fibre
  {E : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  E) (i : aspis_core.r0.domain.FibreIndex) :
  Result (aspis_core.r0.domain.Point E)
  := do
  aspis_core.r0.domain.fibre_point aspis_corer0scalarCodeFieldInst i

end R1Z.ProverRwP7FibreSource
