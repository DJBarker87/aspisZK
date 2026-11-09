import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisS1M31Embedding

/-- [aspis_core::field::M31]
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field.rs', lines 23:0-23:14
    Name pattern: [aspis_core::field::M31]
    Visibility: public -/
@[reducible, rust_type "aspis_core::field::M31"]
def aspis_core.field.M31 := Std.U32

/-- [aspis_core::field::CM31]
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field.rs', lines 255:0-255:15
    Name pattern: [aspis_core::field::CM31]
    Visibility: public -/
@[rust_type "aspis_core::field::CM31"]
structure aspis_core.field.CM31 where
  a : aspis_core.field.M31
  b : aspis_core.field.M31

/-- [aspis_core::field::QM31]
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field.rs', lines 432:0-432:15
    Name pattern: [aspis_core::field::QM31]
    Visibility: public -/
@[rust_type "aspis_core::field::QM31"]
structure aspis_core.field.QM31 where
  c0 : aspis_core.field.CM31
  c1 : aspis_core.field.CM31

/-- [aspis_core::field::wide_exact::WideExact]
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field/wide_exact.rs', lines 28:0-28:20
    Name pattern: [aspis_core::field::wide_exact::WideExact]
    Visibility: public -/
@[rust_type "aspis_core::field::wide_exact::WideExact"]
structure aspis_core.field.wide_exact.WideExact where
  c0 : aspis_core.field.QM31
  c1 : aspis_core.field.QM31

/-- [aspis_core::field::wide_exact::canonical_qm31::closure]
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field/wide_exact.rs', lines 284:17-284:25
    Name pattern: [aspis_core::field::wide_exact::canonical_qm31::closure] -/
@[reducible, rust_type
  "aspis_core::field::wide_exact::canonical_qm31::closure"]
def aspis_core.field.wide_exact.canonical_qm31.closure := Unit


/-- [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field.rs', lines 869:4-869:24
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::QM31}::ZERO"]
def aspis_core.field.QM31.ZERO : aspis_core.field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_core::field::P]
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field.rs', lines 19:0-19:16
    Name pattern: [aspis_core::field::P]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::wide_exact::canonical_qm31::{impl core::ops::function::Fn<(aspis_core::field::M31,), aspis_core::field::M31> for aspis_core::field::wide_exact::canonical_qm31::closure}::call]:
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field/wide_exact.rs', lines 284:17-284:25
    Name pattern: [aspis_core::field::wide_exact::canonical_qm31::{core::ops::function::Fn<aspis_core::field::wide_exact::canonical_qm31::closure, (aspis_core::field::M31), aspis_core::field::M31>}::call] -/
@[rust_fun
  "aspis_core::field::wide_exact::canonical_qm31::{core::ops::function::Fn<aspis_core::field::wide_exact::canonical_qm31::closure, (aspis_core::field::M31), aspis_core::field::M31>}::call"]
def
  aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
  (c : aspis_core.field.wide_exact.canonical_qm31.closure)
  (tupled_args : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← tupled_args % aspis_core.field.P
  ok i

/-- [aspis_core::field::wide_exact::canonical_qm31]:
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field/wide_exact.rs', lines 283:0-283:38
    Name pattern: [aspis_core::field::wide_exact::canonical_qm31] -/
@[rust_fun "aspis_core::field::wide_exact::canonical_qm31"]
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

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_qm31]:
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field/wide_exact.rs', lines 73:4-73:41
    Name pattern: [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_qm31]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_qm31"]
def aspis_core.field.wide_exact.WideExact.from_qm31
  (value : aspis_core.field.QM31) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let q ← aspis_core.field.wide_exact.canonical_qm31 value
  ok { c0 := q, c1 := aspis_core.field.QM31.ZERO }

/-- [aspis_core::field::{aspis_core::field::M31}::ZERO]
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field.rs', lines 55:4-55:23
    Name pattern: [aspis_core::field::{aspis_core::field::M31}::ZERO]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::M31}::ZERO"]
def aspis_core.field.M31.ZERO : aspis_core.field.M31 := 0#u32

/-- [aspis_core::field::{aspis_core::field::CM31}::ZERO]
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field.rs', lines 261:4-261:24
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::ZERO]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::CM31}::ZERO"]
def aspis_core.field.CM31.ZERO : aspis_core.field.CM31 :=
  { a := 0#u32, b := 0#u32 }

/-- [aspis_core::field::{aspis_core::field::CM31}::from_m31]:
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field.rs', lines 276:4-276:35
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::from_m31]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::from_m31"]
def aspis_core.field.CM31.from_m31
  (a : aspis_core.field.M31) : Result aspis_core.field.CM31 := do
  ok { a, b := aspis_core.field.M31.ZERO }

/-- [aspis_core::field::{aspis_core::field::QM31}::from_cm31]:
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/field.rs', lines 891:4-891:38
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::from_cm31]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::from_cm31"]
def aspis_core.field.QM31.from_cm31
  (c0 : aspis_core.field.CM31) : Result aspis_core.field.QM31 := do
  ok { c0, c1 := aspis_core.field.CM31.ZERO }

/-- [aspis_core::r0::scalar::{impl aspis_core::r0::scalar::CodeField for aspis_core::field::M31}::from_m31]:
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/r0/scalar.rs', lines 43:4-43:35
    Name pattern: [aspis_core::r0::scalar::{aspis_core::r0::scalar::CodeField<aspis_core::field::M31>}::from_m31]
    Visibility: public -/
@[rust_fun
  "aspis_core::r0::scalar::{aspis_core::r0::scalar::CodeField<aspis_core::field::M31>}::from_m31"]
def aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31
  (value : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  let i ← value % aspis_core.field.P
  ok i

/-- [aspis_core::r0::scalar::{impl aspis_core::r0::scalar::CodeField for aspis_core::field::CM31}::from_m31]:
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/r0/scalar.rs', lines 58:4-58:35
    Name pattern: [aspis_core::r0::scalar::{aspis_core::r0::scalar::CodeField<aspis_core::field::CM31>}::from_m31]
    Visibility: public -/
@[rust_fun
  "aspis_core::r0::scalar::{aspis_core::r0::scalar::CodeField<aspis_core::field::CM31>}::from_m31"]
def aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31
  (value : aspis_core.field.M31) : Result aspis_core.field.CM31 := do
  let m ←
    aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31 value
  aspis_core.field.CM31.from_m31 m

/-- [aspis_core::r0::scalar::{impl aspis_core::r0::scalar::CodeField for aspis_core::field::QM31}::from_m31]:
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/r0/scalar.rs', lines 72:4-72:35
    Name pattern: [aspis_core::r0::scalar::{aspis_core::r0::scalar::CodeField<aspis_core::field::QM31>}::from_m31]
    Visibility: public -/
@[rust_fun
  "aspis_core::r0::scalar::{aspis_core::r0::scalar::CodeField<aspis_core::field::QM31>}::from_m31"]
def aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31
  (value : aspis_core.field.M31) : Result aspis_core.field.QM31 := do
  let c ←
    aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31 value
  aspis_core.field.QM31.from_cm31 c

/-- [aspis_core::r0::scalar::{impl aspis_core::r0::scalar::CodeField for aspis_core::field::wide_exact::WideExact}::from_m31]:
    Source: '/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core/src/r0/scalar.rs', lines 89:4-89:35
    Name pattern: [aspis_core::r0::scalar::{aspis_core::r0::scalar::CodeField<aspis_core::field::wide_exact::WideExact>}::from_m31]
    Visibility: public -/
@[rust_fun
  "aspis_core::r0::scalar::{aspis_core::r0::scalar::CodeField<aspis_core::field::wide_exact::WideExact>}::from_m31"]
def
  aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
  (value : aspis_core.field.M31) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let q ←
    aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31 value
  aspis_core.field.wide_exact.WideExact.from_qm31 q

/-- [aspis_s1_source_m31_embedding_v1::source_from_m31]:
    Source: 'src/lib.rs', lines 3:0-3:88
    Visibility: public -/
def source_from_m31
  (value : aspis_core.field.M31) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
    value


#print axioms source_from_m31
end AspisS1M31Embedding
