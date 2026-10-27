import RPt_FIq_Native10
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::semantic_packed]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1157:0-1197:1 -/
def pool_v1.pair_forest_semantic_terminal.semantic_packed
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result (Array field.QM31 24#usize)
  := do
  let packed := Array.repeat 24#usize field.QM31.ZERO
  let packed1 ←
    pool_v1.pair_forest_semantic_terminal.add_schedule_lanes packed public1
      openings selectors
  let packed2 ←
    pool_v1.pair_forest_semantic_terminal.add_path_lanes packed1 openings
      selectors
  let packed3 ←
    pool_v1.pair_forest_semantic_terminal.add_value_lanes packed2 openings
      selectors
  let packed4 ←
    pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes packed3 public1
      openings selectors
  let a ←
    pool_v1.pair_forest_semantic_terminal.public_digest_lanes public1 openings
      selectors
  let packed5 ←
    pool_v1.pair_forest_semantic_terminal.add_preweighted packed4 84#usize a
  let q ← Array.index_usize openings.z 1#usize
  let q1 ← pool_v1.pair_forest_semantic_terminal.lift_m31 public1.asset_id
  let asset_difference ← field.QM31.sub q q1
  let i ← 2#usize * 16#usize
  let i1 ← i + 12#usize
  let q2 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i1
  let input_asset ← field.QM31.mul q2 asset_difference
  let i2 ← 31#usize * 16#usize
  let i3 ← i2 + 12#usize
  let q3 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
  let output_scalar ← field.QM31.mul q3 asset_difference
  let i4 ← 28#usize * 16#usize
  let i5 ← i4 + 12#usize
  let q4 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i5
  let private_transfer_term ← field.QM31.mul q4 asset_difference
  let withdrawal_amount_value ←
    lift (core.option.Option.unwrap_or public1.withdrawal_amount 0#u32)
  let i6 ←
    16#usize * pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK
  let i7 ← i6 + 2#usize
  let q5 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i7
  let q6 ← Array.index_usize openings.z 10#usize
  let q7 ←
    pool_v1.pair_forest_semantic_terminal.lift_m31 withdrawal_amount_value
  let q8 ← field.QM31.sub q6 q7
  let withdrawal_term ← field.QM31.mul q5 q8
  let b := core.option.Option.is_some public1.withdrawal_amount
  let scalars ←
    pool_v1.pair_forest_semantic_terminal.scalar_lanes public1.variant b
      input_asset output_scalar private_transfer_term withdrawal_term
  pool_v1.pair_forest_semantic_terminal.add_preweighted packed5 92#usize
    scalars

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::poseidon_selectors]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 225:0-230:1 -/
def pool_v1.pair_forest_semantic_terminal.poseidon_selectors
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result state_only_poseidon.StateOnlyPoseidonSelectors
  := do
  let s ←
    lift (Array.to_slice
      (Array.make 1#usize [
        ({ start := 0#usize, «end» := 57#usize } : core.ops.range.Range
        Std.Usize)
        ]))
  let q ← pool_v1.pair_forest_semantic_terminal.sum_high selectors s
  ok { block := q, «local» := selectors.low }

/-- [aspis_r1_mask_extraction_probe::pool_v1::format::POOL_V1_TREE_DEPTH]
    Source: 'src/statement/pool_v1/format.rs', lines 28:0-28:41
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.format.POOL_V1_TREE_DEPTH : Std.Usize := 20#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_tree_profile::POOL_V1_PAIR_TREE_DEPTH]
    Source: 'src/statement/pool_v1/pair_tree_profile.rs', lines 33:0-33:62
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH : Std.Usize :=
  pool_v1.format.POOL_V1_TREE_DEPTH

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_tree_profile::POOL_V1_PAIR_CAPACITY]
    Source: 'src/statement/pool_v1/pair_tree_profile.rs', lines 35:0-35:71
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY : Result Std.U64 :=
  1#u64 <<< pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::validate_transition]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 209:4-223:1 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.validate_transition_loop
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (iter : core.ops.range.Range Std.Usize) (carry : Std.Usize) :
  Result (core.result.Result Unit
    pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (core.result.Result.Ok ())
  | some level =>
    if level = carry
    then
      if carry < 20#usize
      then
        pool_v1.pair_forest_semantic_terminal.validate_transition_loop public1
          iter1 carry
      else
        let (iter2, expected) ←
          if level < carry
          then
            do
            let expected1 ←
              pool_v1.pair_forest_semantic_terminal.empty_root level
            ok (iter1, expected1)
          else
            do
            let i ←
              public1.transition.live_snapshot.next_pair_index >>> level
            let i1 ← lift (i &&& 1#u64)
            let a ←
              if i1 = 0#u64
              then pool_v1.pair_forest_semantic_terminal.empty_root level
              else
                Array.index_usize public1.transition.live_snapshot.frontier
                  level
            ok (iter1, a)
        let a ←
          Array.index_usize
            public1.transition.candidate_afterstate.next_frontier level
        let b ←
          core.array.equality.PartialEqArray.ne
            field.M31.Insts.CoreCmpPartialEqM31 a expected
        if b
        then
          ok (core.result.Result.Err
            pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
        else
          pool_v1.pair_forest_semantic_terminal.validate_transition_loop
            public1 iter2 carry
    else
      let (iter2, expected) ←
        if level < carry
        then
          do
          let expected1 ←
            pool_v1.pair_forest_semantic_terminal.empty_root level
          ok (iter1, expected1)
        else
          do
          let i ← public1.transition.live_snapshot.next_pair_index >>> level
          let i1 ← lift (i &&& 1#u64)
          let a ←
            if i1 = 0#u64
            then pool_v1.pair_forest_semantic_terminal.empty_root level
            else
              Array.index_usize public1.transition.live_snapshot.frontier level
          ok (iter1, a)
      let a ←
        Array.index_usize public1.transition.candidate_afterstate.next_frontier
          level
      let b ←
        core.array.equality.PartialEqArray.ne
          field.M31.Insts.CoreCmpPartialEqM31 a expected
      if b
      then
        ok (core.result.Result.Err
          pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
      else
        pool_v1.pair_forest_semantic_terminal.validate_transition_loop public1
          iter2 carry
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::validate_transition]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 194:0-223:1 -/
def pool_v1.pair_forest_semantic_terminal.validate_transition
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic) :
  Result (core.result.Result Unit
    pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  := do
  let b ←
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      public1.transition.live_snapshot.pool public1.pool
  if b
  then
    ok (core.result.Result.Err
      pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
  else
    let b1 ←
      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
        public1.transition.live_snapshot.deployment_domain
        public1.deployment_domain
    if b1
    then
      ok (core.result.Result.Err
        pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
    else
      if public1.transition.live_snapshot.sequence !=
        public1.transition.live_snapshot.next_pair_index
      then
        ok (core.result.Result.Err
          pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
      else
        let i ← pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
        if public1.transition.live_snapshot.next_pair_index >= i
        then
          ok (core.result.Result.Err
            pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
        else
          let o ←
            lift (U64.checked_add
              public1.transition.live_snapshot.next_pair_index 1#u64)
          let b2 ←
            core.cmp.PartialEq.ne.trait_default
              (core.option.Option.Insts.CoreCmpPartialEqOption
              core.cmp.PartialEqU64) o (some
              public1.transition.candidate_afterstate.next_pair_index)
          if b2
          then
            ok (core.result.Result.Err
              pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
          else
            let carry ←
              pool_v1.pair_forest_semantic_terminal.bounded_append_carry
                public1.transition.live_snapshot.next_pair_index
            pool_v1.pair_forest_semantic_terminal.validate_transition_loop
              public1 { start := 0#usize, «end» := 20#usize } carry

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::SELECTED_H1_COLUMN]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 56:0-57:88 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
  : Result Std.Usize :=
  pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    + state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::SELECTED_G_COLUMN]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 58:0-58:56 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN
  : Result Std.Usize := do
  let i ← pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
  i + 1#usize


end FIq_Native
