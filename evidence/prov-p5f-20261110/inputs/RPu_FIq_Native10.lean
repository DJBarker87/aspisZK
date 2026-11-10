import RPu_FIq_Native09
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::path_lanes_literal]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 431:4-439:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 427:0-441:1 -/
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

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::sum_high]: loop 1:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 174:8-176:9 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0
  (iter : core.ops.range.Range Std.Usize)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) (sum : field.QM31)
  :
  Result (pool_v1.pair_forest_copy_terminal.Selectors × field.QM31)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (selectors, sum)
  | some block =>
    let q ← Array.index_usize selectors.high block
    let sum1 ← field.QM31.add sum q
    pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0 iter1 selectors
      sum1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::sum_high]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 173:4-177:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.sum_high_loop0
  (iter : core.slice.iter.Iter (core.ops.range.Range Std.Usize))
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) (sum : field.QM31)
  :
  Result field.QM31
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok sum
  | some range =>
    let iter2 ←
      core.ops.range.Range.Insts.CoreCloneClone.clone core.clone.CloneUsize
        range
    let (selectors1, sum1) ←
      pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0 iter2
        selectors sum
    pool_v1.pair_forest_semantic_terminal.sum_high_loop0 iter1 selectors1 sum1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::sum_high]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 171:0-179:1 -/
def pool_v1.pair_forest_semantic_terminal.sum_high
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
  (ranges : Slice (core.ops.range.Range Std.Usize)) :
  Result field.QM31
  := do
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      ranges
  pool_v1.pair_forest_semantic_terminal.sum_high_loop0 iter selectors
    field.QM31.ZERO

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_path_lanes]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 408:0-424:1 -/
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
  let q ← pool_v1.pair_forest_semantic_terminal.sum_high selectors s
  let q1 ← Array.index_usize selectors.low 1#usize
  let q2 ← Array.index_usize selectors.low 5#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize selectors.low 9#usize
  let q5 ← field.QM31.add q3 q4
  let q6 ← Array.index_usize selectors.low 13#usize
  let q7 ← field.QM31.add q5 q6
  let path_selector ← field.QM31.mul q q7
  let path ←
    pool_v1.pair_forest_semantic_terminal.path_lanes_literal path_selector
      openings
  pool_v1.pair_forest_semantic_terminal.add_preweighted packed 32#usize path

/-- [aspis_r1_mask_extraction_probe::spend::DOMAIN_NOTE]
    Source: 'src/statement/spend.rs', lines 16:0-16:53 -/
@[global_simps, irreducible]
def spend.DOMAIN_NOTE : field.M31 := 1095958531#u32

/-- [aspis_r1_mask_extraction_probe::spend::DOMAIN_NULLIFIER]
    Source: 'src/statement/spend.rs', lines 15:0-15:58 -/
@[global_simps, irreducible]
def spend.DOMAIN_NULLIFIER : field.M31 := 1095958530#u32

/-- [aspis_r1_mask_extraction_probe::spend::DOMAIN_OWNER_KEY]
    Source: 'src/statement/spend.rs', lines 14:0-14:58 -/
@[global_simps, irreducible]
def spend.DOMAIN_OWNER_KEY : field.M31 := 1095958529#u32

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::absorption_lanes_literal::closure<'_0, '_1, '_2, '_3, '_4, '_5>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 338:51-347:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 338:51-347:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 338:51-347:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 338:51-347:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 330:0-348:1 -/
def pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal
  (low : field.QM31) (fixed : field.QM31) (chunk_two : field.QM31)
  (chunk_eight : field.QM31) (nodes : field.QM31)
  (openings : Array field.QM31 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
    pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    field.QM31.ZERO (fixed, chunk_two, chunk_eight, nodes, low, openings)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption::closure<'_0, '_1, '_2>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 277:69-283:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 277:69-283:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 277:69-283:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 277:69-283:5 -/
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

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::initial_variant_selectors]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 233:0-253:1 -/
def pool_v1.pair_forest_semantic_terminal.initial_variant_selectors
  (variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant)
  (high27 : field.QM31) (high28 : field.QM31) (high29 : field.QM31) :
  Result (field.QM31 × field.QM31 × field.QM31 × field.QM31)
  := do
  match variant with
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer =>
    let q ← field.QM31.add high27 high28
    ok (high27, field.QM31.ZERO, q, high29)
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal =>
    let q ← field.QM31.add high27 high28
    let q1 ← field.QM31.add q high29
    ok (field.QM31.ZERO, q1, field.QM31.ZERO, field.QM31.ZERO)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_initial_and_absorption]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 255:0-327:1 -/
def pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result ((Array field.QM31 16#usize) × (Array field.QM31 16#usize))
  := do
  let s ←
    lift (Array.to_slice
      (Array.make 2#usize [
        ({ start := 4#usize, «end» := 25#usize } : core.ops.range.Range
        Std.Usize), ({ start := 33#usize, «end» := 57#usize } :
        core.ops.range.Range Std.Usize)
        ]))
  let nodes ← pool_v1.pair_forest_semantic_terminal.sum_high selectors s
  let q ← Array.index_usize selectors.high 0#usize
  let q1 ← Array.index_usize selectors.high 1#usize
  let q2 ← field.QM31.add q q1
  let q3 ← Array.index_usize selectors.high 25#usize
  let q4 ← field.QM31.add q2 q3
  let q5 ← Array.index_usize selectors.high 30#usize
  let first_common ← field.QM31.add q4 q5
  let q6 ← Array.index_usize selectors.high 27#usize
  let q7 ← Array.index_usize selectors.high 28#usize
  let q8 ← Array.index_usize selectors.high 29#usize
  let (transfer_first, fixed, private_chunk_eight, private_chunk_two) ←
    pool_v1.pair_forest_semantic_terminal.initial_variant_selectors
      public1.variant q6 q7 q8
  let q9 ← Array.index_usize selectors.low 0#usize
  let q10 ← field.QM31.add first_common transfer_first
  let q11 ← field.QM31.add q10 fixed
  let full_initial_selector ← field.QM31.mul q9 q11
  let rate_initial_selector ← field.QM31.mul q9 nodes
  let full ← field.PreparedQm31Multiplier.new full_initial_selector
  let q12 ← field.QM31.add full_initial_selector rate_initial_selector
  let full_or_rate ← field.PreparedQm31Multiplier.new q12
  let initial ←
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO (full_or_rate, openings, full)
  let q13 ← field.QM31.add q1 q5
  let note_first ← field.QM31.add q13 transfer_first
  let q14 ← field.QM31.mul_m31 q spend.DOMAIN_OWNER_KEY
  let q15 ← field.QM31.mul_m31 note_first spend.DOMAIN_NOTE
  let q16 ← field.QM31.add q14 q15
  let q17 ← field.QM31.mul_m31 q3 spend.DOMAIN_NULLIFIER
  let domain ← field.QM31.add q16 q17
  let q18 ← field.QM31.mul_m31 q 8#u32
  let q19 ← field.QM31.mul_m31 note_first 18#u32
  let q20 ← field.QM31.add q18 q19
  let q21 ← field.QM31.mul_m31 q3 16#u32
  let length ← field.QM31.add q20 q21
  let q22 ← Array.index_usize initial poseidon2.RATE
  let q23 ← field.QM31.mul q9 domain
  let q24 ← field.QM31.sub q22 q23
  let initial1 ← Array.update initial poseidon2.RATE q24
  let i ← poseidon2.RATE + 1#usize
  let q25 ← Array.index_usize initial1 i
  let q26 ← field.QM31.mul q9 length
  let q27 ← field.QM31.sub q25 q26
  let initial2 ← Array.update initial1 i q27
  let q28 ← field.QM31.add q q1
  let q29 ← Array.index_usize selectors.high 2#usize
  let q30 ← field.QM31.add q28 q29
  let q31 ← field.QM31.add q30 q3
  let q32 ← Array.index_usize selectors.high 26#usize
  let q33 ← field.QM31.add q31 q32
  let q34 ← field.QM31.add q33 q5
  let q35 ← Array.index_usize selectors.high 31#usize
  let chunk_eight ← field.QM31.add q34 q35
  let q36 ← Array.index_usize selectors.high 3#usize
  let q37 ← Array.index_usize selectors.high 32#usize
  let chunk_two ← field.QM31.add q36 q37
  let chunk_eight1 ← field.QM31.add chunk_eight private_chunk_eight
  let chunk_two1 ← field.QM31.add chunk_two private_chunk_two
  let q38 ← Array.index_usize selectors.low 12#usize
  let absorption ←
    pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal q38 fixed
      chunk_two1 chunk_eight1 nodes openings.z
  ok (initial2, absorption)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_schedule_lanes]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 396:0-405:1 -/
def pool_v1.pair_forest_semantic_terminal.add_schedule_lanes
  (packed : Array field.QM31 24#usize)
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result (Array field.QM31 24#usize)
  := do
  let (initial, absorption) ←
    pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption
      public1 openings selectors
  let packed1 ←
    pool_v1.pair_forest_semantic_terminal.add_preweighted packed 0#usize
      initial
  pool_v1.pair_forest_semantic_terminal.add_preweighted packed1 16#usize
    absorption


end FIq_Native
