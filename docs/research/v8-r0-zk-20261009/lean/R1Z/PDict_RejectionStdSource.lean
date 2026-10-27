import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PDict_RejectionStdSource
open Aeneas Aeneas.Std Result ProverRwFull
/-- The emitted Option discriminant is structural: None=0,Some=1. -/
def optionTag {T : Type} : Option T → Isize
  | none => 0#isize
  | some _ => 1#isize

/-- [core::option::{core::option::Option<T>}::is_some_and]:
    Source: '/rustc/library/core/src/option.rs', lines 658:4-658:96
    Name pattern: [core::option::{core::option::Option<@T>}::is_some_and]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::is_some_and"]
def core.option.Option.is_some_and
  {T : Type} {T1 : Type} (opsfunctionFnOnceT1TupleTBoolInst :
  core.ops.function.FnOnce T1 T Bool) (self : Option T) (f : T1) :
  Result Bool
  := do
  match self with
  | none => ok false
  | some x => opsfunctionFnOnceT1TupleTBoolInst.call_once f x

/-- [core::option::{core::option::Option<T>}::as_ref]:
    Source: '/rustc/library/core/src/option.rs', lines 741:4-741:44
    Name pattern: [core::option::{core::option::Option<@T>}::as_ref]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::as_ref"]
def core.option.Option.as_ref
  {T : Type} (self : Option T) : Result (Option T) := do
  match self with
  | none => ok none
  | some _ => ok self

/-- [core::option::{core::option::Option<T>}::ok_or]:
    Source: '/rustc/library/core/src/option.rs', lines 1334:4-1334:73
    Name pattern: [core::option::{core::option::Option<@T>}::ok_or]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) :
  Result (core.result.Result T E)
  := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

/-- [core::option::{impl core::cmp::PartialEq<core::option::Option<T>> for core::option::Option<T>}::eq]:
    Source: '/rustc/library/core/src/option.rs', lines 2440:4-2440:38
    Name pattern: [core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq]
    Visibility: public -/
@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
  {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (self : Option T)
  (other : Option T) :
  Result Bool
  := do
  match self with
  | none => let other1 := optionTag other
            ok (other1 = 0#isize)
  | some l =>
    match other with
    | none => ok false
    | some r => cmpPartialEqInst.eq l r

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
  let i := optionTag o
  massert (i = 0#isize)
  ok none

/-- [core::result::{core::result::Result<T, E>}::map]:
    Source: '/rustc/library/core/src/result.rs', lines 831:4-833:53
    Name pattern: [core::result::{core::result::Result<@T, @E>}::map]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
def core.result.Result.map
  {T : Type} {E : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
  core.ops.function.FnOnce F T U) (self : core.result.Result T E) (op : F) :
  Result (core.result.Result U E)
  := do
  match self with
  | core.result.Result.Ok t =>
    let t1 ← opsfunctionFnOnceFTupleTUInst.call_once op t
    ok (core.result.Result.Ok t1)
  | core.result.Result.Err e => ok (core.result.Result.Err e)


end R1Z.PDict_RejectionStdSource
