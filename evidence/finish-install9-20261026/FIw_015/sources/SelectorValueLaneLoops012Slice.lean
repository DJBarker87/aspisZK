import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import AspisR1SelectedMaskProbe.Funs
import EqualityValueSlice
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::StateOnlyPoseidonOpenings]
    Source: 'src/statement/state_only_poseidon.rs', lines 43:0-47:1
    Visibility: public -/
structure state_only_poseidon.StateOnlyPoseidonOpenings where
  z : Array field.QM31 16#usize
  succ_z : Array field.QM31 16#usize
  xor12_z : Array field.QM31 16#usize


/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 479:4-482:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (range : Array field.QM31 33#usize) (index : Std.Usize) :
  Result (state_only_poseidon.StateOnlyPoseidonOpenings × (Array field.QM31
    33#usize))
  := do
  if index < 10#usize
  then
    let q ← Array.index_usize openings.z index
    let q1 ← field.QM31.square q
    let q2 ← field.QM31.sub q1 q
    let a ← Array.update range index q2
    let index1 ← index + 1#usize
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 openings a
      index1
  else ok (openings, range)
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes]: loop 1:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 484:4-489:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (range : Array field.QM31 33#usize) (index : Std.Usize) :
  Result (state_only_poseidon.StateOnlyPoseidonOpenings × (Array field.QM31
    33#usize))
  := do
  if index < 10#usize
  then
    let q ← Array.index_usize openings.succ_z index
    let q1 ← field.QM31.square q
    let q2 ← field.QM31.sub q1 q
    let i ← 10#usize + index
    let a ← Array.update range i q2
    let index1 ← index + 1#usize
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 openings a
      index1
  else ok (openings, range)
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes]: loop 2:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 491:4-496:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (range : Array field.QM31 33#usize) (index : Std.Usize) :
  Result (state_only_poseidon.StateOnlyPoseidonOpenings × (Array field.QM31
    33#usize))
  := do
  if index < 10#usize
  then
    let q ← Array.index_usize openings.xor12_z index
    let q1 ← field.QM31.square q
    let q2 ← field.QM31.sub q1 q
    let i ← 20#usize + index
    let a ← Array.update range i q2
    let index1 ← index + 1#usize
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings a
      index1
  else ok (openings, range)
partial_fixpoint


end AspisR1SelectedMaskProbe
