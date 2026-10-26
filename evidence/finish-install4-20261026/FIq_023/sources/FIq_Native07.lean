import FIq_Native06
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_full_pair_packed]:
    Source: 'src/statement/state_only_poseidon.rs', lines 509:0-527:1 -/
def state_only_poseidon.interpolated_full_pair_packed
  (state : Array field.QM31 16#usize) (local1 : Array field.QM31 16#usize) :
  Result (Array field.QM31 4#usize)
  := do
  let q ← Array.index_usize local1 1#usize
  let q1 ← Array.index_usize local1 9#usize
  let q2 ← Array.index_usize local1 10#usize
  let a ← Array.index_usize poseidon2.EXTERNAL_INITIAL 2#usize
  let a1 ← Array.index_usize poseidon2.EXTERNAL_FINAL 0#usize
  let a2 ← Array.index_usize poseidon2.EXTERNAL_FINAL 2#usize
  let even ←
    state_only_poseidon.interpolate_three_constant_columns
      (Array.make 3#usize [ q, q1, q2 ]) a a1 a2
  let a3 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 3#usize
  let a4 ← Array.index_usize poseidon2.EXTERNAL_FINAL 1#usize
  let a5 ← Array.index_usize poseidon2.EXTERNAL_FINAL 3#usize
  let odd ←
    state_only_poseidon.interpolate_three_constant_columns
      (Array.make 3#usize [ q, q1, q2 ]) a3 a4 a5
  let a6 ← state_only_poseidon.full_round state even
  state_only_poseidon.full_round_packed a6 odd

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round_m31_constants_packed]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 380:4-383:5 -/
@[rust_loop]
def state_only_poseidon.full_round_m31_constants_packed_loop
  (iter : core.ops.range.Range Std.Usize) (state : Array field.QM31 16#usize)
  (constants1 : Array Std.U32 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok state
  | some lane =>
    let q ← Array.index_usize state lane
    let i ← Array.index_usize constants1 lane
    let m ← field.M31.add q.c0.a i
    let (q1, index_mut_back) ← Array.index_mut_usize state lane
    let state1 := index_mut_back { q1 with c0 := { q1.c0 with a := m } }
    let q2 ← Array.index_usize state1 lane
    let q3 ← state_only_poseidon.pow5 q2
    let a ← Array.update state1 lane q3
    state_only_poseidon.full_round_m31_constants_packed_loop iter1 a constants1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round_m31_constants_packed]:
    Source: 'src/statement/state_only_poseidon.rs', lines 376:0-385:1 -/
def state_only_poseidon.full_round_m31_constants_packed
  (state : Array field.QM31 16#usize) (constants1 : Array Std.U32 16#usize) :
  Result (Array field.QM31 4#usize)
  := do
  let state1 ←
    state_only_poseidon.full_round_m31_constants_packed_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state
      constants1
  state_only_poseidon.external_linear_packed state1

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round_m31_constants]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 356:4-359:5 -/
@[rust_loop]
def state_only_poseidon.full_round_m31_constants_loop
  (iter : core.ops.range.Range Std.Usize) (state : Array field.QM31 16#usize)
  (constants1 : Array Std.U32 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok state
  | some lane =>
    let q ← Array.index_usize state lane
    let i ← Array.index_usize constants1 lane
    let m ← field.M31.add q.c0.a i
    let (q1, index_mut_back) ← Array.index_mut_usize state lane
    let state1 := index_mut_back { q1 with c0 := { q1.c0 with a := m } }
    let q2 ← Array.index_usize state1 lane
    let q3 ← state_only_poseidon.pow5 q2
    let a ← Array.update state1 lane q3
    state_only_poseidon.full_round_m31_constants_loop iter1 a constants1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round_m31_constants]:
    Source: 'src/statement/state_only_poseidon.rs', lines 352:0-362:1 -/
def state_only_poseidon.full_round_m31_constants
  (state : Array field.QM31 16#usize) (constants1 : Array Std.U32 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let state1 ←
    state_only_poseidon.full_round_m31_constants_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state
      constants1
  state_only_poseidon.external_linear_lazy state1

/-- [aspis_r1_mask_extraction_probe::poseidon2::RATE]
    Source: 'src/statement/poseidon2.rs', lines 57:0-57:26
    Visibility: public -/
@[global_simps, irreducible] def poseidon2.RATE : Std.Usize := 8#usize

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::leading_pair_packed]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 410:4-412:5 -/
@[rust_loop]
def state_only_poseidon.leading_pair_packed_loop
  (iter : core.ops.range.Range Std.Usize) (a : Array field.QM31 16#usize)
  (state : Array field.QM31 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok state
  | some lane =>
    let q ← Array.index_usize state lane
    let q1 ← Array.index_usize a lane
    let q2 ← field.QM31.add q q1
    let a1 ← Array.update state lane q2
    state_only_poseidon.leading_pair_packed_loop iter1 a a1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::leading_pair_packed]:
    Source: 'src/statement/state_only_poseidon.rs', lines 406:0-418:1 -/
def state_only_poseidon.leading_pair_packed
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings) :
  Result (Array field.QM31 4#usize)
  := do
  let state ←
    state_only_poseidon.leading_pair_packed_loop
      { start := 0#usize, «end» := poseidon2.RATE } openings.xor12_z
      openings.z
  let state1 ← state_only_poseidon.external_linear_lazy state
  let a ← Array.index_usize poseidon2.EXTERNAL_INITIAL 0#usize
  let a1 ← state_only_poseidon.full_round_m31_constants state1 a
  let a2 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 1#usize
  state_only_poseidon.full_round_m31_constants_packed a1 a2

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected]:
    Source: 'src/statement/state_only_poseidon.rs', lines 590:0-622:1
    Visibility: public -/
def state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : state_only_poseidon.StateOnlyPoseidonSelectors) :
  Result (Array field.QM31 4#usize)
  := do
  let leading_low ← Array.index_usize selectors.«local» 0#usize
  let ii ←
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
      (Array.make 3#usize [ 1#usize, 9#usize, 10#usize ])
  let full_low ←
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
      state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31
      ii field.QM31.ZERO selectors
  let ri ← core.ops.range.RangeInclusive.new 2#usize 8#usize
  let internal_low ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold
      core.iter.range.StepUsize
      state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31
      ri field.QM31.ZERO selectors
  let leading ← state_only_poseidon.leading_pair_packed openings
  let full ←
    state_only_poseidon.interpolated_full_pair_packed openings.z
      selectors.«local»
  let internal ←
    state_only_poseidon.interpolated_internal_pair openings.z
      selectors.«local»
  let prepared_weights ←
    core.array.Array.map (BuiltinFnMut field.QM31 field.PreparedQm31Multiplier)
      (Array.make 3#usize [ leading_low, full_low, internal_low ])
      (field.PreparedQm31Multiplier.new)
  let prepared_block ← field.PreparedQm31Multiplier.new selectors.block
  array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    field.QM31.ZERO (openings, internal, prepared_block, prepared_weights,
    leading, full)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 29:0-29:65
    Visibility: public -/
@[global_simps, irreducible]
def
  pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
  : Std.Usize :=
  16#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 31:0-32:92
    Visibility: public -/
@[global_simps, irreducible]
def
  pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
  : Result Std.Usize := do
  let i ←
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
      + state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  i + 2#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::selected_claim]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1199:0-1205:1 -/
def pool_v1.pair_forest_semantic_terminal.selected_claim
  (claims : Array field.QM31 84#usize) (point : Std.Usize) (column : Std.Usize)
  :
  Result field.QM31
  := do
  let i ←
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
  let i1 ← point * i
  let i2 ← i1 + column
  Array.index_usize claims i2

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1261:67-1267:5 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3)
  := do
  let i ←
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
      + tupled_args
  let q ← pool_v1.pair_forest_semantic_terminal.selected_claim c 0#usize i
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1261:67-1267:5 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1261:67-1267:5 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3 Std.Usize
  field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1261:67-1267:5 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3 Std.Usize
  field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1259:64-1259:106 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2)
  := do
  let q ←
    pool_v1.pair_forest_semantic_terminal.selected_claim c 2#usize tupled_args
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1259:64-1259:106 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1259:64-1259:106 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2 Std.Usize
  field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1259:64-1259:106 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2 Std.Usize
  field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1258:63-1258:105 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1)
  := do
  let q ←
    pool_v1.pair_forest_semantic_terminal.selected_claim c 1#usize tupled_args
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1258:63-1258:105 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1258:63-1258:105 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1 Std.Usize
  field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1258:63-1258:105 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1 Std.Usize
  field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1257:58-1257:100 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure)
  := do
  let q ←
    pool_v1.pair_forest_semantic_terminal.selected_claim c 0#usize tupled_args
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1257:58-1257:100 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q


end FIq_Native
