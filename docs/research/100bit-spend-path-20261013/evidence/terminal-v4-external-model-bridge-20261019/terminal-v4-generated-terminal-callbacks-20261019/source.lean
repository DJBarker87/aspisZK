import AspisR1SelectedMaskProbe.Types
import TerminalStandardOperationModelsV1

/-! Exact closure definitions copied from v4 generated Funs.lean lines 946–1001.
This target checks their use with the existing executable Result.map/map_err
models without compiling the complete generated Funs module. -/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::PoolV1PairForestSemanticTerminalErrorV1,), aspis_r1_mask_extraction_probe::state_only_prefix::r0::Error> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure#2<'a>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2098:21-2098:38 -/
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error.call_once
  (c : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2)
  (tupled_args :
  pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  :
  Result state_only_prefix.r0.Error
  := do
  ok state_only_prefix.r0.Error.Public

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::PoolV1PairForestSemanticTerminalErrorV1,), aspis_r1_mask_extraction_probe::state_only_prefix::r0::Error> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure#2<'a>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2098:21-2098:38 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2
  pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
  state_only_prefix.r0.Error := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error.call_once
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<((aspis_r1_mask_extraction_probe::field::QM31, [aspis_r1_mask_extraction_probe::field::QM31; 16usize], [aspis_r1_mask_extraction_probe::field::QM31; 10usize], aspis_r1_mask_extraction_probe::field::QM31),), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure#1<'a>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2097:17-2097:32 -/
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1)
  (tupled_args : (field.QM31 × (Array field.QM31 16#usize) × (Array
  field.QM31 10#usize) × field.QM31)) :
  Result field.QM31
  := do
  let (q, _, _, _) := tupled_args
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<((aspis_r1_mask_extraction_probe::field::QM31, [aspis_r1_mask_extraction_probe::field::QM31; 16usize], [aspis_r1_mask_extraction_probe::field::QM31; 10usize], aspis_r1_mask_extraction_probe::field::QM31),), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure#1<'a>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2097:17-2097:32 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1
  (field.QM31 × (Array field.QM31 16#usize) × (Array field.QM31 10#usize) ×
  field.QM31) field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31.call_once
}

abbrev TerminalCallbackInput :=
  field.QM31 × (Array field.QM31 16#usize) ×
    (Array field.QM31 10#usize) × field.QM31

abbrev TerminalCallbackIntermediate :=
  core.result.Result TerminalCallbackInput
    pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1

abbrev TerminalCallbackOutput :=
  core.result.Result field.QM31 state_only_prefix.r0.Error

def terminalCallbacksMapThenMapErr (r : TerminalCallbackIntermediate) :
    Result TerminalCallbackOutput := do
  let mapped ← core.result.Result.map
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31
    r ()
  core.result.Result.map_err
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error
    mapped ()

theorem terminalCallbacksMapThenMapErr_ok
    (x : TerminalCallbackInput) :
    terminalCallbacksMapThenMapErr (.Ok x) = .ok (.Ok x.1) := by
  simp [terminalCallbacksMapThenMapErr,
    core.result.Result.map, core.result.Result.map_err,
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31,
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31.call_once,
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error,
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error.call_once]

theorem terminalCallbacksMapThenMapErr_error (e :
    pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1) :
    terminalCallbacksMapThenMapErr (.Err e) = .ok (.Err state_only_prefix.r0.Error.Public) := by
  simp [terminalCallbacksMapThenMapErr,
    core.result.Result.map, core.result.Result.map_err,
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31,
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31.call_once,
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error,
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error.call_once]

#print axioms terminalCallbacksMapThenMapErr_ok
#print axioms terminalCallbacksMapThenMapErr_error

end AspisR1SelectedMaskProbe
