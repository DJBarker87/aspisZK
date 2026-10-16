import SelectorValueLaneGeneratedSlice
import SelectorValueLaneIndexedSlice
import SelectorValueLaneLoops012Slice
import PreweightedLoopSlice
import SelectorArrayMapRuntimeSlice

/-! Exact generated enclosing add_value_lanes declaration from the sealed
indexed source candidate. Only helper-reference qualification and the enclosing
namespace are adapted to the already checked isolated source modules. The
adapter is invertible; it does not replace the function body with a model. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ValueLaneCandidate
open AspisR1SelectedMaskProbe

def pool_v1.pair_forest_semantic_terminal.add_value_lanes
  (packed : Array field.QM31 24#usize)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result (Array field.QM31 24#usize)
  := do
  let value_selectors ←
    core.array.Array.map
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      (Array.make 3#usize [ 0#usize, 2#usize, 4#usize ]) selectors
  let q ← Array.index_usize value_selectors 0#usize
  let q1 ← field.QM31.add field.QM31.ZERO q
  let q2 ← Array.index_usize value_selectors 1#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize value_selectors 2#usize
  let range_selector ← field.QM31.add q3 q4
  let range := Array.repeat 33#usize field.QM31.ZERO
  let (openings1, range1) ←
    AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 openings range
      0#usize
  let (openings2, range2) ←
    AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 openings1
      range1 0#usize
  let (openings3, range3) ←
    AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings2
      range2 0#usize
  let q5 ← AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.z
  let q6 ←
    AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.succ_z
  let i ← 1#u32 <<< 10#i32
  let q7 ← field.QM31.mul_m31 q6 i
  let q8 ← field.QM31.add q5 q7
  let q9 ←
    AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.xor12_z
  let i1 ← 1#u32 <<< 20#i32
  let q10 ← field.QM31.mul_m31 q9 i1
  let reconstructed ← field.QM31.add q8 q10
  let q11 ← Array.index_usize openings3.z 10#usize
  let q12 ← field.QM31.sub q11 reconstructed
  let range4 ← Array.update range3 30#usize q12
  let q13 ← Array.index_usize openings3.succ_z 10#usize
  let range5 ← Array.update range4 31#usize q13
  let q14 ← Array.index_usize openings3.xor12_z 10#usize
  let a ← Array.update range5 32#usize q14
  let range6 ←
    AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3 range_selector
      a 0#usize
  let packed1 ←
    AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted packed 49#usize
      range6
  let i2 ←
    16#usize * AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK
  let i3 ← i2 + 6#usize
  let conservation_selector ←
    AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
  let q15 ← Array.index_usize openings3.z 0#usize
  let q16 ← Array.index_usize openings3.z 1#usize
  let q17 ← field.QM31.sub q15 q16
  let q18 ← Array.index_usize openings3.z 2#usize
  let q19 ← field.QM31.sub q17 q18
  let q20 ← field.QM31.mul conservation_selector q19
  let q21 ← Array.index_usize openings3.succ_z 0#usize
  let q22 ← Array.index_usize openings3.succ_z 1#usize
  let q23 ← field.QM31.sub q21 q22
  let q24 ← field.QM31.mul conservation_selector q23
  AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted packed1 82#usize
    (Array.make 2#usize [ q20, q24 ])

end AspisR1ValueLaneCandidate
