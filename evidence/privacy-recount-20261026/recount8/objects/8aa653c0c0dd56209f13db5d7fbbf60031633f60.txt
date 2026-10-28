import R1Z.ProverRwDictionaryBytesSource
import R1Z.ProverRwDictionaryOptionSource
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace R1Z.ProverRwSuccessParserSource
abbrev aspis_core.field.P := ProverRwDictionaryBytesSource.aspis_core.field.P
def aspis_core.field.M31.from_le_bytes
  (bytes : Array Std.U8 4#usize) : Result (Option aspis_core.field.M31) := do
  let v ← lift (core.num.U32.from_le_bytes bytes)
  if v >= aspis_core.field.P
  then ok none
  else ok (some v)

def aspis_core.field.CM31.from_le_bytes
  (bytes : Slice Std.U8) : Result (Option aspis_core.field.CM31) := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) bytes { start := 0#usize, «end» := 4#usize }
  let r ←
    core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
  match r with
  | core.result.Result.Ok value =>
    let o ← aspis_core.field.M31.from_le_bytes value
    let cf ← ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch o
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
        let o1 ← aspis_core.field.M31.from_le_bytes value1
        let cf1 ← ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          ok (some { a := val, b := val1 })
        | core.ops.control_flow.ControlFlow.Break residual =>
          ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
            aspis_core.field.CM31 residual
      | core.result.Result.Err _ => ok none
    | core.ops.control_flow.ControlFlow.Break residual =>
      ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        aspis_core.field.CM31 residual
  | core.result.Result.Err _ => ok none

def aspis_core.field.QM31.from_le_bytes
  (bytes : Slice Std.U8) : Result (Option aspis_core.field.QM31) := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) bytes { start := 0#usize, «end» := 8#usize }
  let o ← aspis_core.field.CM31.from_le_bytes s
  let cf ← ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) bytes { start := 8#usize, «end» := 16#usize }
    let o1 ← aspis_core.field.CM31.from_le_bytes s1
    let cf1 ← ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      ok (some { c0 := val, c1 := val1 })
    | core.ops.control_flow.ControlFlow.Break residual =>
      ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        aspis_core.field.QM31 residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      aspis_core.field.QM31 residual
end R1Z.ProverRwSuccessParserSource
