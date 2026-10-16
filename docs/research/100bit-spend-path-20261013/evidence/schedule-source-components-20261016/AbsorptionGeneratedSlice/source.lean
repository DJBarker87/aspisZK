import ArrayFromFnCopySlice
import SelectorValueLaneGeneratedSlice
import SelectedClaimGatherSlice

/-! Exact generated absorption callback, traits and array wrapper. Only the
module framing and isolating namespace are changed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1AbsorptionCandidate
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal::closure]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 327:51-336:5 -/
def pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure :=
  field.QM31 × field.QM31 × field.QM31 × field.QM31 × field.QM31 × Array
  field.QM31 16#usize

/-- [aspis_r1_mask_extraction_probe::poseidon2::RATE]
    Source: 'src/statement/poseidon2.rs', lines 57:0-57:26
    Visibility: public -/
@[global_simps, irreducible] def poseidon2.RATE : Std.Usize := 8#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal::closure<'_0, '_1, '_2, '_3, '_4, '_5>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 327:51-336:5 -/
def
  pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure)
  := do
  let (blocks, q, q1, q2, q3, a) := c
  let blocks1 ←
    if tupled_args < 2#usize
    then ok blocks
    else
      if tupled_args < poseidon2.RATE
      then field.QM31.add blocks q
      else
        do
        let q4 ← field.QM31.add blocks q
        let q5 ← field.QM31.add q4 q1
        field.QM31.add q5 q2
  let q4 ← field.QM31.mul q3 blocks1
  let q5 ← Array.index_usize a tupled_args
  let q6 ← field.QM31.mul q4 q5
  ok (q6, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal::closure<'_0, '_1, '_2, '_3, '_4, '_5>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 327:51-336:5 -/
def
  pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal::closure<'_0, '_1, '_2, '_3, '_4, '_5>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 327:51-336:5 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure
  Std.Usize field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal::closure<'_0, '_1, '_2, '_3, '_4, '_5>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 327:51-336:5 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure
  Std.Usize field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 319:0-337:1 -/
def pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal
  (low : field.QM31) (fixed : field.QM31) (chunk_two : field.QM31)
  (chunk_eight : field.QM31) (nodes : field.QM31)
  (openings : Array field.QM31 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
    pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    field.QM31.ZERO (fixed, chunk_two, chunk_eight, nodes, low, openings)

end AspisR1AbsorptionCandidate
