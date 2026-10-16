import SumHighGeneratedSlice
import PathLaneGeneratedSlice
import PreweightedLoopSlice

/-! Whole actual generated enclosing add_path_lanes candidate declaration.
Only helper-reference qualification and the namespace are adapted; the
inverse map recovers every original declaration byte. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1PathEnclosingCandidate
open AspisR1SelectedMaskProbe

def pool_v1.pair_forest_semantic_terminal.add_path_lanes
  (packed : Array field.QM31 24#usize)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result (Array field.QM31 24#usize)
  := do
  let s ←
    lift (Array.to_slice
      (Array.make 1#usize [
        ({ start := 57#usize, «end» := 63#usize } : core.ops.range.Range
        Std.Usize)
        ]))
  let q ← AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high selectors s
  let q1 ← Array.index_usize selectors.low 1#usize
  let q2 ← Array.index_usize selectors.low 5#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize selectors.low 9#usize
  let q5 ← field.QM31.add q3 q4
  let q6 ← Array.index_usize selectors.low 13#usize
  let q7 ← field.QM31.add q5 q6
  let path_selector ← field.QM31.mul q q7
  let path ←
    AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal path_selector
      openings
  AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted packed 32#usize path

end AspisR1PathEnclosingCandidate
