import FIo_Install
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1.FIp_DotDecode
abbrev field.M31 := U32
abbrev field.CM31 := FIo_Native.aspis_core.field.CM31
abbrev field.QM31 := FIo_Native.aspis_core.field.QM31
/-- Source-bound Option discriminant support: the R245/R255 Option type row
has None=0 and Some=1, both signed Isize. This fills the pinned builtin
instance gap; it does not alter any of the three generated bodies. -/
def optionTag {T : Type} : Option T → Isize
  | none => 0#isize
  | some _ => 1#isize
local instance optionDiscriminant {T : Type} : Discriminant (Option T) Isize where
  read_discriminant := optionTag




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

/-- [aspis_core::field::P]
    Source: 'field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::{aspis_core::field::M31}::from_le_bytes]:
    Source: 'field.rs', lines 239:4-246:5
    Visibility: public -/
def field.M31.from_le_bytes
  (bytes : Array Std.U8 4#usize) : Result (Option field.M31) := do
  let v ← lift (core.num.U32.from_le_bytes bytes)
  if v >= field.P
  then ok none
  else ok (some v)

/-- [aspis_core::field::{aspis_core::field::CM31}::from_le_bytes]:
    Source: 'field.rs', lines 410:4-422:5
    Visibility: public -/
def field.CM31.from_le_bytes
  (bytes : Slice Std.U8) : Result (Option field.CM31) := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) bytes { start := 0#usize, «end» := 4#usize }
  let r ←
    core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
  match r with
  | core.result.Result.Ok value =>
    let o ← field.M31.from_le_bytes value
    let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
          { start := 4#usize, «end» := 8#usize }
      let r1 ←
        core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s1
      match r1 with
      | core.result.Result.Ok value1 =>
        let o1 ← field.M31.from_le_bytes value1
        let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          ok (some { a := val, b := val1 })
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
            field.CM31 residual
      | core.result.Result.Err _ => ok none
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        field.CM31 residual
  | core.result.Result.Err _ => ok none

/-- [aspis_core::field::{aspis_core::field::QM31}::from_le_bytes]:
    Source: 'field.rs', lines 1022:4-1026:5
    Visibility: public -/
def field.QM31.from_le_bytes
  (bytes : Slice Std.U8) : Result (Option field.QM31) := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) bytes { start := 0#usize, «end» := 8#usize }
  let o ← field.CM31.from_le_bytes s
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) bytes { start := 8#usize, «end» := 16#usize }
    let o1 ← field.CM31.from_le_bytes s1
    let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      ok (some { c0 := val, c1 := val1 })
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        field.QM31 residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      field.QM31 residual


#print axioms field.M31.from_le_bytes
#print axioms field.QM31.from_le_bytes
end AspisR1.FIp_DotDecode
