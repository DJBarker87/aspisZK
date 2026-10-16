import ArrayFromFnCopySlice
import SelectorValueLaneGeneratedSlice
import SelectedClaimGatherSlice
import SelectorValueLaneLoops012Slice

/-! Exact generated initial-array callback and traits. Only the
module framing and isolating namespace are changed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1InitialCandidate
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption::closure]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 266:69-272:5 -/
def pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure
  :=
  field.PreparedQm31Multiplier × state_only_poseidon.StateOnlyPoseidonOpenings
  × field.PreparedQm31Multiplier

/-- [aspis_r1_mask_extraction_probe::poseidon2::RATE]
    Source: 'src/statement/poseidon2.rs', lines 57:0-57:26
    Visibility: public -/
@[global_simps, irreducible] def poseidon2.RATE : Std.Usize := 8#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption::closure<'_0, '_1, '_2>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 266:69-272:5 -/
def
  pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c :
  pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure)
  := do
  let (pqm, sopo, pqm1) := c
  if tupled_args < poseidon2.RATE
  then
    let q ← Array.index_usize sopo.z tupled_args
    let q1 ← field.PreparedQm31Multiplier.mul pqm q
    ok (q1, c)
  else
    let q ← Array.index_usize sopo.z tupled_args
    let q1 ← field.PreparedQm31Multiplier.mul pqm1 q
    ok (q1, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption::closure<'_0, '_1, '_2>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 266:69-272:5 -/
def
  pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c :
  pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption::closure<'_0, '_1, '_2>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 266:69-272:5 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure
  Std.Usize field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption::closure<'_0, '_1, '_2>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 266:69-272:5 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure
  Std.Usize field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

end AspisR1InitialCandidate
