import Aeneas
import AspisR156FullFreeze.FunsCore
import AspisR239CoeffExecutionRaw

open Aeneas Aeneas.Std Result
open AspisR156FullFreeze AspisR239CoeffExecutionRaw
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option autoImplicit false

namespace AspisR286QueryFieldRaw

/-- [aspis_core::field::{aspis_core::field::QM31}::neg]:
    Source: '/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a/crates/aspis-core/src/field.rs', lines 874:4-874:28
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::neg]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::neg"]
def aspis_core.field.QM31.neg
  (self : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let c ← aspis_core.field.CM31.neg self.c0
  let c1 ← aspis_core.field.CM31.neg self.c1
  ok { c0 := c, c1 }

/-- [aspis_core::field::{aspis_core::field::QM31}::mul_m31]:
    Source: '/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a/crates/aspis-core/src/field.rs', lines 927:4-927:42
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

#print axioms aspis_core.field.QM31.neg
#print axioms aspis_core.field.QM31.mul_m31

end AspisR286QueryFieldRaw
