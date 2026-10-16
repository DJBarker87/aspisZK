import SelectorValueLaneGeneratedSlice
import SelectorValueLaneLoops012Slice

/-! Exact generated path residual loop and wrapper, isolated by namespace.
The retained declarations are byte-for-byte source slices. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1PathLaneCandidate
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::poseidon2::RATE]
    Source: 'src/statement/poseidon2.rs', lines 57:0-57:26
    Visibility: public -/
@[global_simps, irreducible] def poseidon2.RATE : Std.Usize := 8#usize

/-- [aspis_r1_mask_extraction_probe::poseidon2::DIGEST_ELEMS]
    Source: 'src/statement/poseidon2.rs', lines 58:0-58:34
    Visibility: public -/
@[global_simps, irreducible] def poseidon2.DIGEST_ELEMS : Std.Usize := 8#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::path_lanes_literal]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 420:4-428:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop
  (iter : core.ops.range.Range Std.Usize) (path_selector : field.QM31)
  (a : Array field.QM31 16#usize) (a1 : Array field.QM31 16#usize)
  (bit : field.QM31) (path : Array field.QM31 17#usize) :
  Result (Array field.QM31 17#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok path
  | some lane =>
    let i ← 1#usize + lane
    let current ← Array.index_usize a i
    let q ← field.QM31.sub field.QM31.ONE bit
    let q1 ← field.QM31.mul path_selector q
    let q2 ← Array.index_usize a1 lane
    let q3 ← field.QM31.sub q2 current
    let q4 ← field.QM31.mul q1 q3
    let path1 ← Array.update path i q4
    let q5 ← field.QM31.mul path_selector bit
    let i1 ← poseidon2.RATE + lane
    let q6 ← Array.index_usize a1 i1
    let q7 ← field.QM31.sub q6 current
    let q8 ← field.QM31.mul q5 q7
    let i2 ← 1#usize + poseidon2.DIGEST_ELEMS
    let i3 ← i2 + lane
    let a2 ← Array.update path1 i3 q8
    pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop iter1
      path_selector a a1 bit a2
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::path_lanes_literal]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 416:0-430:1 -/
def pool_v1.pair_forest_semantic_terminal.path_lanes_literal
  (path_selector : field.QM31)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings) :
  Result (Array field.QM31 17#usize)
  := do
  let bit ← Array.index_usize openings.z 0#usize
  let path := Array.repeat 17#usize field.QM31.ZERO
  let q ← field.QM31.sub bit field.QM31.ONE
  let q1 ← field.QM31.mul bit q
  let q2 ← field.QM31.mul path_selector q1
  let a ← Array.update path 0#usize q2
  pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop
    { start := 0#usize, «end» := poseidon2.DIGEST_ELEMS } path_selector
    openings.z openings.succ_z bit a

end AspisR1PathLaneCandidate
