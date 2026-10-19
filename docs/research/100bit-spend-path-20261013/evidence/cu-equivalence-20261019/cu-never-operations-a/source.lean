import AspisR1CuArraySource.NeverTypes
-- Exact successful emitted declaration cuts; bodies unchanged.
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1CuArraySource
/-- [core::ops::try_trait::{impl core::ops::try_trait::FromResidual<core::ops::try_trait::NeverShortCircuitResidual> for core::ops::try_trait::NeverShortCircuit<T>}::from_residual]:
    Source: '/rustc/library/core/src/ops/try_trait.rs', lines 450:4-450:62
    Name pattern: [core::ops::try_trait::{core::ops::try_trait::FromResidual<core::ops::try_trait::NeverShortCircuit<@T>, core::ops::try_trait::NeverShortCircuitResidual>}::from_residual]
    Visibility: public -/
@[rust_fun
  "core::ops::try_trait::{core::ops::try_trait::FromResidual<core::ops::try_trait::NeverShortCircuit<@T>, core::ops::try_trait::NeverShortCircuitResidual>}::from_residual"]
def
  core.ops.try_trait.NeverShortCircuit.Insts.CoreOpsTry_traitFromResidualNeverShortCircuitResidual.from_residual
  (T : Type) (never : core.ops.try_trait.NeverShortCircuitResidual) :
  Result (core.ops.try_trait.NeverShortCircuit T)
  := do
  fail panic

/-- Trait implementation: [core::ops::try_trait::{impl core::ops::try_trait::FromResidual<core::ops::try_trait::NeverShortCircuitResidual> for core::ops::try_trait::NeverShortCircuit<T>}]
    Source: '/rustc/library/core/src/ops/try_trait.rs', lines 448:0-448:51
    Name pattern: [core::ops::try_trait::FromResidual<core::ops::try_trait::NeverShortCircuit<@T>, core::ops::try_trait::NeverShortCircuitResidual>] -/
@[reducible, rust_trait_impl
  "core::ops::try_trait::FromResidual<core::ops::try_trait::NeverShortCircuit<@T>, core::ops::try_trait::NeverShortCircuitResidual>"]
def
  core.ops.try_trait.NeverShortCircuit.Insts.CoreOpsTry_traitFromResidualNeverShortCircuitResidual
  (T : Type) : core.ops.try_trait.FromResidual
  (core.ops.try_trait.NeverShortCircuit T)
  core.ops.try_trait.NeverShortCircuitResidual := {
  from_residual :=
    core.ops.try_trait.NeverShortCircuit.Insts.CoreOpsTry_traitFromResidualNeverShortCircuitResidual.from_residual
    T
}

/-- [core::ops::try_trait::{impl core::ops::try_trait::Try for core::ops::try_trait::NeverShortCircuit<T>}::from_output]:
    Source: '/rustc/library/core/src/ops/try_trait.rs', lines 443:4-443:32
    Name pattern: [core::ops::try_trait::{core::ops::try_trait::Try<core::ops::try_trait::NeverShortCircuit<@T>>}::from_output]
    Visibility: public -/
@[rust_fun
  "core::ops::try_trait::{core::ops::try_trait::Try<core::ops::try_trait::NeverShortCircuit<@T>>}::from_output"]
def core.ops.try_trait.NeverShortCircuit.Insts.CoreOpsTry_traitTry.from_output
  {T : Type} (x : T) : Result (core.ops.try_trait.NeverShortCircuit T) := do
  ok x

/-- [core::ops::try_trait::{impl core::ops::try_trait::Try for core::ops::try_trait::NeverShortCircuit<T>}::branch]:
    Source: '/rustc/library/core/src/ops/try_trait.rs', lines 438:4-438:64
    Name pattern: [core::ops::try_trait::{core::ops::try_trait::Try<core::ops::try_trait::NeverShortCircuit<@T>>}::branch]
    Visibility: public -/
@[rust_fun
  "core::ops::try_trait::{core::ops::try_trait::Try<core::ops::try_trait::NeverShortCircuit<@T>>}::branch"]
def core.ops.try_trait.NeverShortCircuit.Insts.CoreOpsTry_traitTry.branch
  {T : Type} (self : core.ops.try_trait.NeverShortCircuit T) :
  Result (core.ops.control_flow.ControlFlow
    core.ops.try_trait.NeverShortCircuitResidual T)
  := do
  ok (core.ops.control_flow.ControlFlow.Continue self)

end AspisR1CuArraySource
