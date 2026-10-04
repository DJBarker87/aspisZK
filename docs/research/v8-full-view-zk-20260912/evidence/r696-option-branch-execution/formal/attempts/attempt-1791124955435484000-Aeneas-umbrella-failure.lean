import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR664OwnedFoldOptionWrappers

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

theorem branch_none (T : Type) :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch (none : Option T) =
      .ok (.Break none) := by
  rfl

#print axioms branch_none

theorem branch_some (T : Type) (v : T) :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch (some v) =
      .ok (.Continue v) := by
  rfl

#print axioms branch_some

theorem branch_exact (T : Type) (o : Option T) :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch o =
      match o with
      | none => .ok (.Break none)
      | some v => .ok (.Continue v) := by
  cases o <;> rfl

#print axioms branch_exact

theorem residual_none (T : Type) :
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      T none = .ok none := by
  rfl

#print axioms residual_none

theorem residual_all (T : Type) (o : Option core.convert.Infallible) :
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      T o = .ok none := by
  cases o with
  | none => rfl
  | some impossible => cases impossible

#print axioms residual_all

end AspisR664OwnedFoldOptionWrappers
