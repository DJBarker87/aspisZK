-- Exact declaration slice from the pinned combined from_fn candidate Funs.lean.
-- The source blocks are byte-exact; only imports and namespace framing are adapted.
import Aeneas.Std
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.Funs
import SelectedClaimSlice
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::field::{impl core::clone::Clone for aspis_r1_mask_extraction_probe::field::QM31}::clone]:
    Source: 'src/field.rs', lines 431:9-431:14
    Visibility: public -/
def field.QM31.Insts.CoreCloneClone.clone
  (self : field.QM31) : Result field.QM31 := do
  ok self

/-- Trait implementation: [aspis_r1_mask_extraction_probe::field::{impl core::clone::Clone for aspis_r1_mask_extraction_probe::field::QM31}]
    Source: 'src/field.rs', lines 431:9-431:14 -/
@[reducible]
def field.QM31.Insts.CoreCloneClone : core.clone.Clone field.QM31 := {
  clone := field.QM31.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::field::{impl core::marker::Copy for aspis_r1_mask_extraction_probe::field::QM31}]
    Source: 'src/field.rs', lines 431:16-431:20 -/
@[reducible]
def field.QM31.Insts.CoreMarkerCopy : core.marker.Copy field.QM31 := {
  cloneInst := field.QM31.Insts.CoreCloneClone
}
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure<'a, '_1>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2071:74-2071:100 -/
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure<'a, '_1>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2071:74-2071:100 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure
  Std.Usize field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure<'a, '_1>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2071:74-2071:100 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure
  Std.Usize field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

end AspisR1SelectedMaskProbe
