import AspisR249R110Raw

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR249R110Raw
open AspisR156FullFreeze

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace AspisR259PrivateInputRaw

/-- [core::option::{impl core::ops::try_trait::Try for core::option::Option<T>}::branch]:
    Source: '/rustc/library/core/src/option.rs', lines 2779:4-2779:64
    Name pattern: [core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch]
    Visibility: public -/
@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch
  {T : Type} (self : Option T) :
  Result (core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T)
  := do
  match self with
  | none => ok (core.ops.control_flow.ControlFlow.Break none)
  | some v => ok (core.ops.control_flow.ControlFlow.Continue v)

/-- [core::option::{impl core::ops::try_trait::FromResidual<core::option::Option<core::convert::Infallible>> for core::option::Option<T>}::from_residual]:
    Source: '/rustc/library/core/src/option.rs', lines 2793:4-2793:67
    Name pattern: [core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual]
    Visibility: public -/
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
def
  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
  (T : Type) (o : Option core.convert.Infallible) : Result (Option T) := do
  let i := read_discriminant o
  massert (i = 0#isize)
  ok none

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::C}::input]:
    Source: '../r110_norm.rs', lines 24:4-24:77 -/
def circle_norm.joined_inverse.line_norm.r110_norm.C.input
  (x : aspis_core.field.CM31) :
  Result (Option circle_norm.joined_inverse.line_norm.r110_norm.C)
  := do
  let o ← circle_norm.joined_inverse.line_norm.r110_norm.B.input x.a
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let o1 ← circle_norm.joined_inverse.line_norm.r110_norm.B.input x.b
    let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 => ok (some (val, val1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        circle_norm.joined_inverse.line_norm.r110_norm.C residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      circle_norm.joined_inverse.line_norm.r110_norm.C residual

#print axioms core.option.Option.Insts.CoreOpsTry_traitTry.branch
#print axioms core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.input

end AspisR259PrivateInputRaw
