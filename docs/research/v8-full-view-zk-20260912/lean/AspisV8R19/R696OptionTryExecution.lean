import Aeneas.Std

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

end AspisR664OwnedFoldOptionWrappers
