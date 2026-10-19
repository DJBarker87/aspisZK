import AspisR1CuArraySource.Types
-- Exact successful emitted declaration cuts; bodies unchanged.
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1CuArraySource
/-- [core::ops::try_trait::NeverShortCircuitResidual]
    Source: '/rustc/library/core/src/ops/try_trait.rs', lines 430:0-430:41
    Name pattern: [core::ops::try_trait::NeverShortCircuitResidual] -/
@[rust_type "core::ops::try_trait::NeverShortCircuitResidual"]
inductive core.ops.try_trait.NeverShortCircuitResidual where

/-- [core::ops::try_trait::NeverShortCircuit]
    Source: '/rustc/library/core/src/ops/try_trait.rs', lines 400:0-400:38
    Name pattern: [core::ops::try_trait::NeverShortCircuit] -/
@[reducible, rust_type "core::ops::try_trait::NeverShortCircuit"]
def core.ops.try_trait.NeverShortCircuit (T : Type) := T

/-- [core::ops::try_trait::{core::ops::try_trait::NeverShortCircuit<T>}::wrap_mut_1::closure]
    Source: '/rustc/library/core/src/ops/try_trait.rs', lines 415:8-415:22
    Name pattern: [core::ops::try_trait::{core::ops::try_trait::NeverShortCircuit<@T>}::wrap_mut_1::closure] -/
@[reducible, rust_type
  "core::ops::try_trait::{core::ops::try_trait::NeverShortCircuit<@T>}::wrap_mut_1::closure"]
def core.ops.try_trait.NeverShortCircuit.wrap_mut_1.closure (T : Type) (A :
  Type) (F : Type) :=
  F

end AspisR1CuArraySource
