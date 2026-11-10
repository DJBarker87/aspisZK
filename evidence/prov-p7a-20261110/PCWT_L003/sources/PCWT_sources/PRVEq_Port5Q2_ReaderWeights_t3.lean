-- PCWT_ binding discharge for AspisR1.Port5Q2_ReaderWeights.weights and weights_loop, route (a)/(b).
-- What was bound (PCVF_ k1): the fresh read_checkpoint_weights text (PCQD_E034, frozen 4bb3b3f, overflow ON) has two externals,
-- QM31::from_le_bytes (crates/aspis-core/src/field.rs, Aspis item) and Vec<QM31>::iter_mut/into_iter (std).  The gate is parametric in `read`.
-- Here the Aspis external is bound to the FRESH frozen decoder chain M31/CM31/QM31::from_le_bytes (text of the NMH emission as compiled in
-- PRVEq_R1CandidateFieldParsers_j1, renamed to the gate universe aspis_core.field.*), and the std external to the gate hand model intoIter.
-- Library items (HM-B): core.slice.iter.IteratorIterMut.next in the loop body, the Vec iter_mut/into_iter model `intoIter`.
import Aeneas
import Port5Q2_ReaderWeights
import PRVEq_Port5Q2_ReaderWeights_k1
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1.Port5Q2_ReaderWeights
namespace PRVFresh_t3

    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::{aspis_core::field::M31}::from_le_bytes]:
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 239:4-246:5
    Visibility: public -/
def aspis_core.field.M31.from_le_bytes
  (bytes : Array Std.U8 4#usize) : Result (Option aspis_core.field.M31) := do
  let v ← lift (core.num.U32.from_le_bytes bytes)
  if v >= aspis_core.field.P
  then ok none
  else ok (some v)

/-- [aspis_core::field::{aspis_core::field::CM31}::from_le_bytes]:
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 410:4-422:5
    Visibility: public -/
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
        let o1 ← aspis_core.field.M31.from_le_bytes value1
        let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          ok (some { a := val, b := val1 })
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
            aspis_core.field.CM31 residual
      | core.result.Result.Err _ => ok none
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        aspis_core.field.CM31 residual
  | core.result.Result.Err _ => ok none

/-- [aspis_core::field::{aspis_core::field::QM31}::from_le_bytes]:
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 1022:4-1026:5
    Visibility: public -/
def aspis_core.field.QM31.from_le_bytes
  (bytes : Slice Std.U8) : Result (Option aspis_core.field.QM31) := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) bytes { start := 0#usize, «end» := 8#usize }
  let o ← aspis_core.field.CM31.from_le_bytes s
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) bytes { start := 8#usize, «end» := 16#usize }
    let o1 ← aspis_core.field.CM31.from_le_bytes s1
    let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      ok (some { c0 := val, c1 := val1 })
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        aspis_core.field.QM31 residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      aspis_core.field.QM31 residual


def x0 : PRVFresh_k1.Ext where
  from_le_bytes := aspis_core.field.QM31.from_le_bytes
  into_iter := AspisR1.Port5Q2_ReaderWeights.intoIter

end PRVFresh_t3
end AspisR1.Port5Q2_ReaderWeights

namespace PRVEq.Port5Q2_t3
open AspisR1.Port5Q2_ReaderWeights

theorem weights_loop_frozen_decoder :
    PRVFresh_k1.verifier.read_checkpoint_weights_loop PRVFresh_t3.x0 =
    AspisR1.Port5Q2_ReaderWeights.weights_loop (PRVFresh_k1.verifier.Reader.k PRVFresh_t3.x0) :=
  PRVEq.Port5Q2_k1.loop_eq PRVFresh_t3.x0

theorem weights_frozen_decoder_and_iter :
    PRVFresh_k1.verifier.read_checkpoint_weights PRVFresh_t3.x0 =
    AspisR1.Port5Q2_ReaderWeights.weights (PRVFresh_k1.verifier.Reader.k PRVFresh_t3.x0) :=
  PRVEq.Port5Q2_k1.weights_eq PRVFresh_t3.x0 rfl

end PRVEq.Port5Q2_t3
#print axioms PRVEq.Port5Q2_t3.weights_loop_frozen_decoder
#print axioms PRVEq.Port5Q2_t3.weights_frozen_decoder_and_iter
