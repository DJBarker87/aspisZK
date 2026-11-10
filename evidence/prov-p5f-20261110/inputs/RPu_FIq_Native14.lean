import RPu_FIq_Native13
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1]
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 18:0-18:66
    Visibility: public -/
@[global_simps, irreducible]
def
  pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1
  : Std.Usize :=
  136#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::evaluate_with_selectors]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 958:4-1063:5 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
  (append_index : Std.U64)
  (variant :
  pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
  (patterns : Array field.QM31 14#usize) (a : Array field.QM31 2#usize)
  (a1 : Array field.QM31 2#usize) (a2 : Array field.QM31 2#usize)
  (a3 : Array field.QM31 2#usize) (link_index : Std.Usize) :
  Result ((Array field.QM31 2#usize) × (Array field.QM31 2#usize) × (Array
    field.QM31 2#usize) × (Array field.QM31 2#usize))
  := do
  if link_index <
    pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1
  then
    let link ←
      Array.index_usize pool_v1.pair_forest_copy_terminal.constants.COPY_LINKS
        link_index
    let weight ←
      pool_v1.pair_forest_copy_terminal.link_weight link append_index variant
    let (a4, a5) ←
      pool_v1.pair_forest_copy_terminal.accumulate_endpoint a a1 link.producer
        link.tag weight patterns selectors
    let (a6, a7) ←
      pool_v1.pair_forest_copy_terminal.accumulate_endpoint a2 a3 link.consumer
        link.tag weight patterns selectors
    let link_index1 ← link_index + 1#usize
    pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop selectors
      append_index variant patterns a4 a5 a6 a7 link_index1
  else ok (a, a1, a2, a3)
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::evaluate_with_selectors]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 924:0-1087:1 -/
def pool_v1.pair_forest_copy_terminal.evaluate_with_selectors
  (openings : Array field.QM31 16#usize) (h1_z : field.QM31)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
  (lambda : field.QM31) (chi : field.QM31) (append_index : Std.U64)
  (variant :
  pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1) :
  Result
    pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1
  := do
  let patterns ←
    pool_v1.pair_forest_copy_terminal.pattern_values openings lambda
  let a := Array.repeat 2#usize field.QM31.ZERO
  let a1 := Array.repeat 2#usize field.QM31.ZERO
  let a2 := Array.repeat 2#usize field.QM31.ZERO
  let a3 := Array.repeat 2#usize field.QM31.ZERO
  let (a4, a5, a6, a7) ←
    pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop selectors
      append_index variant patterns a a1 a2 a3 0#usize
  let active ← pool_v1.pair_forest_copy_terminal.Selectors.active selectors
  let q ←
    pool_v1.pair_forest_copy_terminal.copy_residual
      {
        producer_values := a4,
        producer_weights := a5,
        consumer_values := a6,
        consumer_weights := a7
      } h1_z chi
  let q1 ← field.QM31.mul active q
  ok { residual := q1, active }

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::expand]: loop 1:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 150:12-155:13 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0
  {N : Std.Usize}
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (weights : Array field.QM31 N) (prepared : field.PreparedQm31Multiplier) :
  Result (Array field.QM31 N)
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok weights
  | some index =>
    let parent ← Array.index_usize weights index
    let right ← field.PreparedQm31Multiplier.mul prepared parent
    let q ← field.QM31.sub parent right
    let i ← 2#usize * index
    let weights1 ← Array.update weights i q
    let i1 ← i + 1#usize
    let a ← Array.update weights1 i1 right
    pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0 iter1 a
      prepared
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::expand]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 148:8-157:9 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0
  {N : Std.Usize} (iter : core.slice.iter.Iter field.QM31)
  (weights : Array field.QM31 N) (len : Std.Usize) :
  Result (Array field.QM31 N)
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok weights
  | some coordinate =>
    let prepared ← field.PreparedQm31Multiplier.new coordinate
    let iter2 ←
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator
        core.iter.range.StepUsize) { start := 0#usize, «end» := len }
    let weights1 ←
      pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0 iter2
        weights prepared
    let len1 ← len * 2#usize
    pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0 iter1 weights1
      len1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::expand]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 144:4-159:5 -/
def pool_v1.pair_forest_copy_terminal.Selectors.expand
  (N : Std.Usize) (coordinates : Slice field.QM31) :
  Result (Array field.QM31 N)
  := do
  let weights := Array.repeat N field.QM31.ZERO
  let a ← Array.update weights 0#usize field.QM31.ONE
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      coordinates
  pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0 iter a 1#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::at_point]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 161:4-166:5 -/
def pool_v1.pair_forest_copy_terminal.Selectors.at_point
  (point : Array field.QM31 10#usize) :
  Result pool_v1.pair_forest_copy_terminal.Selectors
  := do
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice field.QM31)) point
      { «end» := 6#usize }
  let a ← pool_v1.pair_forest_copy_terminal.Selectors.expand 64#usize s
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice field.QM31)) point
      { start := 6#usize }
  let a1 ← pool_v1.pair_forest_copy_terminal.Selectors.expand 16#usize s1
  ok { high := a, low := a1 }

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::boxed_at_point]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 169:4-171:5 -/
def pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point
  (point : Array field.QM31 10#usize) :
  Result pool_v1.pair_forest_copy_terminal.Selectors
  := do
  pool_v1.pair_forest_copy_terminal.Selectors.at_point point

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1284:4-1286:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
  (iter : core.iter.adapters.rev.Rev (core.array.iter.IntoIter field.QM31
  24#usize)) (prepared_theta : field.PreparedQm31Multiplier)
  (composition : field.QM31) :
  Result field.QM31
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
      field.QM31 24#usize) iter
  match o with
  | none => ok composition
  | some lane =>
    let q ← field.PreparedQm31Multiplier.mul prepared_theta composition
    let composition1 ← field.QM31.add q lane
    pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 iter1
      prepared_theta composition1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts]: loop 1:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1287:4-1289:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
  (iter : core.iter.adapters.rev.Rev (core.array.iter.IntoIter field.QM31
  4#usize)) (prepared_theta : field.PreparedQm31Multiplier)
  (composition : field.QM31) :
  Result field.QM31
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
      field.QM31 4#usize) iter
  match o with
  | none => ok composition
  | some lane =>
    let q ← field.PreparedQm31Multiplier.mul prepared_theta composition
    let composition1 ← field.QM31.add q lane
    pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 iter1
      prepared_theta composition1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1230:0-1298:1 -/
def pool_v1.pair_forest_semantic_terminal.composition_parts
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (claims : Array field.QM31 84#usize) (point : Array field.QM31 10#usize)
  (lambda : field.QM31) (chi : field.QM31) (theta : field.QM31) :
  Result (core.result.Result (field.QM31 × (Array field.QM31 16#usize) ×
    (Array field.QM31 10#usize) × field.QM31 × field.QM31 × field.QM31)
    pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  := do
  let (o, invalid_amount) ←
    match public1.withdrawal_amount with
    | none => ok (none, false)
    | some amount =>
      do
      let b ←
        if amount = 0#u32
        then ok true
        else do
             let i ← 1#u32 <<< 30#u32
             ok (decide (amount >= i))
      ok (public1.withdrawal_amount, b)
  if invalid_amount
  then
    ok (core.result.Result.Err
      pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidPublicAmount)
  else
    let r ←
      pool_v1.pair_forest_semantic_terminal.validate_transition
        { public1 with withdrawal_amount := o }
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let a ←
        array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
          pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
          field.QM31.ZERO claims
      let a1 ←
        array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
          pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
          field.QM31.ZERO claims
      let a2 ←
        array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
          pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
          field.QM31.ZERO claims
      let mask_only ←
        array_from_fn_copy 10#usize field.QM31.Insts.CoreMarkerCopy
          pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
          field.QM31.ZERO claims
      let selectors ←
        pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point
      let sops ←
        pool_v1.pair_forest_semantic_terminal.poseidon_selectors selectors
      let poseidon ←
        state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
          { z := a, succ_z := a1, xor12_z := a2 } sops
      let semantic ←
        pool_v1.pair_forest_semantic_terminal.semantic_packed
          { public1 with withdrawal_amount := o }
          { z := a, succ_z := a1, xor12_z := a2 } selectors
      let i ← pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
      let h1_z ←
        pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize i
      let pvpfcvv ←
        pool_v1.pair_forest_semantic_terminal.copy_variant public1.variant
      let copy ←
        pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h1_z
          selectors lambda chi public1.transition.live_snapshot.next_pair_index
          pvpfcvv
      let prepared_theta ← field.PreparedQm31Multiplier.new theta
      let ii ←
        Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
          semantic
      let iter ←
        core.iter.traits.iterator.Iterator.rev.trait_default
          (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          field.QM31 24#usize)
          (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
          field.QM31 24#usize) ii
      let composition ←
        pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 iter
          prepared_theta copy.residual
      let ii1 ←
        Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
          poseidon
      let iter1 ←
        core.iter.traits.iterator.Iterator.rev.trait_default
          (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          field.QM31 4#usize)
          (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
          field.QM31 4#usize) ii1
      let composition1 ←
        pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 iter1
          prepared_theta composition
      let i1 ← pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN
      let q ←
        pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize i1
      ok (core.result.Result.Ok (composition1, a, mask_only, q, h1_z,
        copy.active))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (field.QM31 × (Array field.QM31 16#usize) × (Array field.QM31
        10#usize) × field.QM31 × field.QM31 × field.QM31)
        (core.convert.FromSame
        pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
        residual

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::equality_value::{impl core::ops::function::Fn<(aspis_r1_mask_extraction_probe::field::QM31, aspis_r1_mask_extraction_probe::field::QM31), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::equality_value::closure}::call]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1216:17-1219:5 -/
def
  pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
  (c : pool_v1.pair_forest_semantic_terminal.equality_value.closure)
  (tupled_args : (field.QM31 × field.QM31)) :
  Result field.QM31
  := do
  let (a, b) := tupled_args
  let ab ← field.QM31.mul a b
  let q ← field.QM31.sub field.QM31.ONE a
  let q1 ← field.QM31.sub q b
  let q2 ← field.QM31.add q1 ab
  field.QM31.add q2 ab

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::equality_value]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1222:4-1225:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.equality_value_loop
  (left : Array field.QM31 10#usize) (right : Array field.QM31 10#usize)
  (product : field.QM31) (index : Std.Usize) :
  Result field.QM31
  := do
  let s ← lift (Array.to_slice left)
  let i := Slice.len s
  if index < i
  then
    let q ← Array.index_usize left index
    let q1 ← Array.index_usize right index
    let q2 ←
      pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
        () (q, q1)
    let product1 ← field.QM31.mul product q2
    let index1 ← index + 1#usize
    pool_v1.pair_forest_semantic_terminal.equality_value_loop left right
      product1 index1
  else ok product
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::equality_value]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1215:0-1227:1 -/
def pool_v1.pair_forest_semantic_terminal.equality_value
  (left : Array field.QM31 10#usize) (right : Array field.QM31 10#usize) :
  Result field.QM31
  := do
  let q ← Array.index_usize left 0#usize
  let q1 ← Array.index_usize right 0#usize
  let product ←
    pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
      () (q, q1)
  pool_v1.pair_forest_semantic_terminal.equality_value_loop left right product
    1#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::terminal_parts]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1300:0-1325:1 -/
def pool_v1.pair_forest_semantic_terminal.terminal_parts
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (claims : Array field.QM31 84#usize) (point : Array field.QM31 10#usize)
  (lambda : field.QM31) (chi : field.QM31) (theta : field.QM31)
  (zerocheck_point : Array field.QM31 10#usize) (mu : field.QM31) :
  Result (core.result.Result (field.QM31 × (Array field.QM31 16#usize) ×
    (Array field.QM31 10#usize) × field.QM31)
    pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  := do
  let r ←
    pool_v1.pair_forest_semantic_terminal.composition_parts public1 claims
      point lambda chi theta
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (composition, c1, mask_only, g, h1_z, copy_active) := val
    let q ←
      pool_v1.pair_forest_semantic_terminal.equality_value zerocheck_point
        point
    let q1 ← field.QM31.mul q composition
    let q2 ← field.QM31.mul mu h1_z
    let q3 ← field.QM31.add q1 q2
    let q4 ← field.QM31.mul mu mu
    let q5 ← field.QM31.sub field.QM31.ONE copy_active
    let q6 ← field.QM31.mul q5 h1_z
    let q7 ← field.QM31.mul q4 q6
    let original ← field.QM31.add q3 q7
    ok (core.result.Result.Ok (original, c1, mask_only, g))
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (field.QM31 × (Array field.QM31 16#usize) × (Array field.QM31 10#usize)
      × field.QM31) (core.convert.FromSame
      pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
      residual

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2080:8-2099:9
    Visibility: public -/
def pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (claims : Array (Array field.QM31 29#usize) 3#usize)
  (alpha : Array field.QM31 10#usize) (c : state_only_prefix.r0.Challenges) :
  Result (core.result.Result field.QM31 state_only_prefix.r0.Error)
  := do
  let selected ←
    array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO claims
  let sp ← pool_v1.pair_forest_semantic_terminal.r0.Public.semantic self
  let r ←
    pool_v1.pair_forest_semantic_terminal.terminal_parts sp selected alpha
      c.lambda c.chi c.theta c.zc c.mu
  let r1 ←
    core.result.Result.map
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31
      r ()
  core.result.Result.map_err
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error
    r1 ()


end FIq_Native
