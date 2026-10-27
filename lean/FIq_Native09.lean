import FIq_Native08
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::closure<'_0, '_1, '_2, N>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 128:77-135:9 -/
def
  pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {N : Std.Usize}
  (c : pool_v1.pair_forest_semantic_terminal.add_preweighted.closure N)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::closure<'_0, '_1, '_2, N>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 128:77-135:9 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnOnce
  (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure N) Std.Usize
  field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::closure<'_0, '_1, '_2, N>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 128:77-135:9 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnMut
  (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure N) Std.Usize
  field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    N
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 127:4-137:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.add_preweighted_loop
  {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.Usize)
  (packed : Array field.QM31 24#usize) (start : Std.Usize)
  (values : Array field.QM31 N) :
  Result (Array field.QM31 24#usize)
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok packed
  | some group =>
    let lanes ←
      array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
        (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        N) field.QM31.ZERO (group, start, values)
    let q ← Array.index_usize packed group
    let s ← lift (Array.to_slice lanes)
    let q1 ← field.qm31_pack_base4 s
    let q2 ← field.QM31.add q q1
    let a ← Array.update packed group q2
    pool_v1.pair_forest_semantic_terminal.add_preweighted_loop iter1 a start
      values
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 120:0-138:1 -/
def pool_v1.pair_forest_semantic_terminal.add_preweighted
  {N : Std.Usize} (packed : Array field.QM31 24#usize) (start : Std.Usize)
  (values : Array field.QM31 N) :
  Result (Array field.QM31 24#usize)
  := do
  let first ← start / 4#usize
  let i ← start + N
  let i1 ← i - 1#usize
  let last ← i1 / 4#usize
  let iter ← core.ops.range.RangeInclusive.new first last
  pool_v1.pair_forest_semantic_terminal.add_preweighted_loop iter packed start
    values

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::OUTPUT_OCCUPANCY_ROW]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 61:0-61:49 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.OUTPUT_OCCUPANCY_ROW
  : Result Std.Usize := do
  let i ← 63#usize * 16#usize
  i + 10#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::INPUT_OCCUPANCY_ROW]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 60:0-60:47 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.INPUT_OCCUPANCY_ROW
  : Result Std.Usize := do
  let i ← 63#usize * 16#usize
  i + 9#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_occupancy_lanes]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 544:0-568:1 -/
def pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes
  (packed : Array field.QM31 24#usize)
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result (Array field.QM31 24#usize)
  := do
  let i ← pool_v1.pair_forest_semantic_terminal.INPUT_OCCUPANCY_ROW
  let input_occupancy ←
    pool_v1.pair_forest_copy_terminal.Selectors.row selectors i
  let i1 ← pool_v1.pair_forest_semantic_terminal.OUTPUT_OCCUPANCY_ROW
  let output_occupancy ←
    pool_v1.pair_forest_copy_terminal.Selectors.row selectors i1
  let expected_output ←
    pool_v1.pair_forest_semantic_terminal.variant_expected_output
      public1.variant
  let occupancy ←
    pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal
      input_occupancy output_occupancy expected_output openings.z
  pool_v1.pair_forest_semantic_terminal.add_preweighted packed 0#usize
    occupancy

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::VALUE_AUXILIARY_BLOCK]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 59:0-59:40 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK : Std.Usize :=
  63#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes::closure<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 486:27-486:84 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 486:27-486:84 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 486:27-486:84 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 486:27-486:84 -/
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

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::reconstruct_10::{impl core::ops::function::FnMut<(aspis_r1_mask_extraction_probe::field::QM31, &'_ aspis_r1_mask_extraction_probe::field::QM31), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::reconstruct_10::closure}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 186:23-186:56 -/
def
  pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure)
  (tupled_args : (field.QM31 × field.QM31)) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure)
  := do
  let (acc, bit) := tupled_args
  let q ← field.QM31.add acc acc
  let q1 ← field.QM31.add q bit
  ok (q1, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::reconstruct_10::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::field::QM31, &'_ aspis_r1_mask_extraction_probe::field::QM31), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::reconstruct_10::closure}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 186:23-186:56 -/
def
  pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure)
  (p : (field.QM31 × field.QM31)) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::reconstruct_10::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::field::QM31, &'_ aspis_r1_mask_extraction_probe::field::QM31), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::reconstruct_10::closure}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 186:23-186:56 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure (field.QM31 ×
  field.QM31) field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::reconstruct_10::{impl core::ops::function::FnMut<(aspis_r1_mask_extraction_probe::field::QM31, &'_ aspis_r1_mask_extraction_probe::field::QM31), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::reconstruct_10::closure}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 186:23-186:56 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure (field.QM31 ×
  field.QM31) field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::reconstruct_10]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 182:0-187:1 -/
def pool_v1.pair_forest_semantic_terminal.reconstruct_10
  (view : Array field.QM31 16#usize) : Result field.QM31 := do
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice field.QM31)) view
      { «end» := 9#usize }
  let i ← core.slice.Slice.iter s
  let r ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorSliceIter field.QM31)
      (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
      field.QM31) i
  let q ← Array.index_usize view 9#usize
  core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold
    (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
    field.QM31)
    pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31
    r q ()

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 493:4-496:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 498:4-503:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 505:4-510:5 -/
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

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes]: loop 3:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 519:8-521:9 -/
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

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 480:0-533:1 -/
def pool_v1.pair_forest_semantic_terminal.add_value_lanes
  (packed : Array field.QM31 24#usize)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result (Array field.QM31 24#usize)
  := do
  let value_selectors ←
    core.array.Array.map
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
  let (iter, into_iter_back) ←
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
      range6
  let (im, back) ←
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3 iter
      (fun im1 => im1) range_selector
  let im1 := back im
  let range7 := into_iter_back im1
  let packed1 ←
    pool_v1.pair_forest_semantic_terminal.add_preweighted packed 49#usize
      range7
  let i2 ←
    16#usize * pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK
  let i3 ← i2 + 6#usize
  let conservation_selector ←
    pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
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
  pool_v1.pair_forest_semantic_terminal.add_preweighted packed1 82#usize
    (Array.make 2#usize [ q20, q24 ])


end FIq_Native
