import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CompositionGatherClosuresChunk07aV2
import TerminalV4TerminalPartsChunk08V2
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe
abbrev TerminalQM31PartsCaller :=
  pool_v1.pair_forest_semantic_terminal.SemanticPublic →
  Array field.QM31 84#usize → Array field.QM31 10#usize →
  field.QM31 → field.QM31 → field.QM31 → Array field.QM31 10#usize →
  field.QM31 →
  Result (core.result.Result
    (field.QM31 × (Array field.QM31 16#usize) ×
      (Array field.QM31 10#usize) × field.QM31)
    pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1))
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

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure<'a, '_1>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2086:74-2086:100 -/
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure)
  := do
  let i ← tupled_args / 28#usize
  let i1 ← tupled_args % 28#usize
  let a ← Array.index_usize c i
  let q ← Array.index_usize a i1
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure<'a, '_1>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2086:74-2086:100 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2086:74-2086:100 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2086:74-2086:100 -/
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

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2080:8-2099:9
    Visibility: public -/
def pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31_with_callers
  (terminalSemantic : pool_v1.pair_forest_semantic_terminal.r0.Public →
    Result pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (terminalParts : TerminalQM31PartsCaller)
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (claims : Array (Array field.QM31 29#usize) 3#usize)
  (alpha : Array field.QM31 10#usize) (c : state_only_prefix.r0.Challenges) :
  Result (core.result.Result field.QM31 state_only_prefix.r0.Error)
  := do
  let selected ←
    array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO claims
  let sp ← terminalSemantic self
  let r ←
    terminalParts sp selected alpha c.lambda c.chi c.theta c.zc c.mu
  let r1 ←
    core.result.Result.map
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31
      r ()
  core.result.Result.map_err
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error
    r1 ()
end AspisR1SelectedMaskProbe
