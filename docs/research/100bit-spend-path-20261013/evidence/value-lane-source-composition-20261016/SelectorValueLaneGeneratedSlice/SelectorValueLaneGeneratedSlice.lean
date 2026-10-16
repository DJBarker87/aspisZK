import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import SelectorSourceSlice
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

/- Exact generated candidate closure alias from Types.lean lines 366-370. -/
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes::closure]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 472:27-472:84 -/
@[reducible]
def pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure :=
  pool_v1.pair_forest_copy_terminal.Selectors

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::VALUE_AUXILIARY_BLOCK]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 59:0-59:40 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK : Std.Usize :=
  63#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes::closure<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 472:27-472:84 -/
def
  pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure)
  := do
  let i ←
    16#usize * pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK
  let i1 ← i + tupled_args
  let q ← pool_v1.pair_forest_copy_terminal.Selectors.row c i1
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes::closure<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 472:27-472:84 -/
def
  pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes::closure<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 472:27-472:84 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure Std.Usize
  field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes::closure<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 472:27-472:84 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure Std.Usize
  field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes]: loop 3:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 505:8-507:9 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3
  (iter : core.slice.iter.IterMut field.QM31)
  (back : core.slice.iter.IterMut field.QM31 → core.slice.iter.IterMut
  field.QM31) (range_selector : field.QM31) :
  Result ((core.slice.iter.IterMut field.QM31) × (core.slice.iter.IterMut
    field.QM31 → core.slice.iter.IterMut field.QM31))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (iter1, fun im => let im1 := next_back im none
                                 back im1)
  | some residual =>
    let residual1 ← field.QM31.mul range_selector residual
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3 iter1
      (fun im => let im1 := next_back im (some residual1)
                 back im1) range_selector
partial_fixpoint

end AspisR1SelectedMaskProbe
