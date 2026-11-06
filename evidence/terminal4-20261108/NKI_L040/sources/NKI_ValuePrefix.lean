import NDO_JGa_ValueLanes
import NJX_RangeFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValuePrefix
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
structure Tail where
 openings : Openings
 selector : field.QM31
 range : Array field.QM31 33#usize
def run (openings : Openings) (selectors : Selectors) : Result Tail := do
  let value_selectors ←
    FIq_Native.core.array.Array.map
      pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      (Array.make 3#usize [ 0#usize, 2#usize, 4#usize ]) selectors
  let q ← Array.index_usize value_selectors 0#usize
  let q1 ← field.QM31.add field.QM31.ZERO q
  let q2 ← Array.index_usize value_selectors 1#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize value_selectors 2#usize
  let range_selector ← field.QM31.add q3 q4
  let range := Array.repeat 33#usize field.QM31.ZERO
  let (openings1, range1) ←
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 openings range
      0#usize
  let (openings2, range2) ←
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 openings1
      range1 0#usize
  let (openings3, range3) ←
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings2
      range2 0#usize
  let q5 ← pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.z
  let q6 ←
    pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.succ_z
  let i ← 1#u32 <<< 10#i32
  let q7 ← field.QM31.mul_m31 q6 i
  let q8 ← field.QM31.add q5 q7
  let q9 ←
    pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.xor12_z
  let i1 ← 1#u32 <<< 20#i32
  let q10 ← field.QM31.mul_m31 q9 i1
  let reconstructed ← field.QM31.add q8 q10
  let q11 ← Array.index_usize openings3.z 10#usize
  let q12 ← field.QM31.sub q11 reconstructed
  let range4 ← Array.update range3 30#usize q12
  let q13 ← Array.index_usize openings3.succ_z 10#usize
  let range5 ← Array.update range4 31#usize q13
  let q14 ← Array.index_usize openings3.xor12_z 10#usize
  let range6 ← Array.update range5 32#usize q14
  ok ⟨openings3,range_selector,range6⟩
end AspisR1.NKI_ValuePrefix
end
