import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PDict_PureSource
open Aeneas Aeneas.Std Result ProverRwFull

/-- [aspis_core::field::{impl core::cmp::PartialEq<aspis_core::field::M31> for aspis_core::field::M31}::eq]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field.rs', lines 22:22-22:31
    Name pattern: [aspis_core::field::{core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{core::cmp::PartialEq<aspis_core::field::M31, aspis_core::field::M31>}::eq"]
def aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : aspis_core.field.M31) (other : aspis_core.field.M31) :
  Result Bool
  := do
  ok (self = other)

/-- [aspis_core::field::{impl core::cmp::PartialEq<aspis_core::field::CM31> for aspis_core::field::CM31}::eq]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field.rs', lines 254:22-254:31
    Name pattern: [aspis_core::field::{core::cmp::PartialEq<aspis_core::field::CM31, aspis_core::field::CM31>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{core::cmp::PartialEq<aspis_core::field::CM31, aspis_core::field::CM31>}::eq"]
def aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq
  (self : aspis_core.field.CM31) (other : aspis_core.field.CM31) :
  Result Bool
  := do
  let b ← aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq self.a other.a
  if b
  then aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq self.b other.b
  else ok false

/-- [aspis_core::field::{impl core::cmp::PartialEq<aspis_core::field::QM31> for aspis_core::field::QM31}::eq]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field.rs', lines 431:22-431:31
    Name pattern: [aspis_core::field::{core::cmp::PartialEq<aspis_core::field::QM31, aspis_core::field::QM31>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{core::cmp::PartialEq<aspis_core::field::QM31, aspis_core::field::QM31>}::eq"]
def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
  (self : aspis_core.field.QM31) (other : aspis_core.field.QM31) :
  Result Bool
  := do
  let b ←
    aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq self.c0 other.c0
  if b
  then aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq self.c1 other.c1
  else ok false

/-- [aspis_core::circle::{impl core::cmp::PartialEq<aspis_core::circle::SecureCirclePoint> for aspis_core::circle::SecureCirclePoint}::eq]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/circle.rs', lines 10:29-10:38
    Name pattern: [aspis_core::circle::{core::cmp::PartialEq<aspis_core::circle::SecureCirclePoint, aspis_core::circle::SecureCirclePoint>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_core::circle::{core::cmp::PartialEq<aspis_core::circle::SecureCirclePoint, aspis_core::circle::SecureCirclePoint>}::eq"]
def
  aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq
  (self : aspis_core.circle.SecureCirclePoint)
  (other : aspis_core.circle.SecureCirclePoint) :
  Result Bool
  := do
  let b ← aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq self.x other.x
  if b
  then aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq self.y other.y
  else ok false

/-- Trait implementation: [aspis_core::circle::{impl core::cmp::PartialEq<aspis_core::circle::SecureCirclePoint> for aspis_core::circle::SecureCirclePoint}]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/circle.rs', lines 10:29-10:38
    Name pattern: [core::cmp::PartialEq<aspis_core::circle::SecureCirclePoint, aspis_core::circle::SecureCirclePoint>] -/
@[reducible, rust_trait_impl
  "core::cmp::PartialEq<aspis_core::circle::SecureCirclePoint, aspis_core::circle::SecureCirclePoint>"]
def aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint
  : core.cmp.PartialEq aspis_core.circle.SecureCirclePoint
  aspis_core.circle.SecureCirclePoint := {
  eq :=
    aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq
}

/-- [aspis_core::field::wide_exact::{impl core::clone::Clone for aspis_core::field::wide_exact::WideExact}::clone]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field/wide_exact.rs', lines 27:9-27:14
    Name pattern: [aspis_core::field::wide_exact::{core::clone::Clone<aspis_core::field::wide_exact::WideExact>}::clone]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::wide_exact::{core::clone::Clone<aspis_core::field::wide_exact::WideExact>}::clone"]
def aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone
  (self : aspis_core.field.wide_exact.WideExact) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  ok self

/-- [aspis_core::field::wide_exact::{impl core::cmp::PartialEq<aspis_core::field::wide_exact::WideExact> for aspis_core::field::wide_exact::WideExact}::eq]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field/wide_exact.rs', lines 27:38-27:47
    Name pattern: [aspis_core::field::wide_exact::{core::cmp::PartialEq<aspis_core::field::wide_exact::WideExact, aspis_core::field::wide_exact::WideExact>}::eq]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::wide_exact::{core::cmp::PartialEq<aspis_core::field::wide_exact::WideExact, aspis_core::field::wide_exact::WideExact>}::eq"]
def aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq
  (self : aspis_core.field.wide_exact.WideExact)
  (other : aspis_core.field.wide_exact.WideExact) :
  Result Bool
  := do
  let b ←
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq self.c0 other.c0
  if b
  then aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq self.c1 other.c1
  else ok false

/-- Trait implementation: [aspis_core::field::wide_exact::{impl core::cmp::PartialEq<aspis_core::field::wide_exact::WideExact> for aspis_core::field::wide_exact::WideExact}]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field/wide_exact.rs', lines 27:38-27:47
    Name pattern: [core::cmp::PartialEq<aspis_core::field::wide_exact::WideExact, aspis_core::field::wide_exact::WideExact>] -/
@[reducible, rust_trait_impl
  "core::cmp::PartialEq<aspis_core::field::wide_exact::WideExact, aspis_core::field::wide_exact::WideExact>"]
def aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact :
  core.cmp.PartialEq aspis_core.field.wide_exact.WideExact
  aspis_core.field.wide_exact.WideExact := {
  eq :=
    aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq
}

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::c0]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field/wide_exact.rs', lines 63:4-63:33
    Name pattern: [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::c0]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::c0"]
def aspis_core.field.wide_exact.WideExact.impl.c0
  (self : aspis_core.field.wide_exact.WideExact) :
  Result aspis_core.field.QM31
  := do
  ok self.c0

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::c1]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field/wide_exact.rs', lines 67:4-67:33
    Name pattern: [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::c1]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::c1"]
def aspis_core.field.wide_exact.WideExact.impl.c1
  (self : aspis_core.field.wide_exact.WideExact) :
  Result aspis_core.field.QM31
  := do
  ok self.c1

/-- [aspis_core::field::{aspis_core::field::CM31}::new]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field.rs', lines 271:4-271:38
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::new]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::new"]
def aspis_core.field.CM31.new
  (a : aspis_core.field.M31) (b : aspis_core.field.M31) :
  Result aspis_core.field.CM31
  := do
  ok { a, b }



#print axioms aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
#print axioms aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq
#print axioms aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
#print axioms aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq
#print axioms aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint
#print axioms aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone
#print axioms aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq
#print axioms aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact
#print axioms aspis_core.field.wide_exact.WideExact.impl.c0
#print axioms aspis_core.field.wide_exact.WideExact.impl.c1
#print axioms aspis_core.field.CM31.new
end PDict_PureSource
