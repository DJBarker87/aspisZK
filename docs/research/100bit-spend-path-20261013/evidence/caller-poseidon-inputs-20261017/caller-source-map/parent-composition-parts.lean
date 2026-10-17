def pool_v1.pair_forest_semantic_terminal.composition_parts
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (claims : Array field.QM31 84#usize) (point : Array field.QM31 10#usize)
  (lambda : field.QM31) (chi : field.QM31) (theta : field.QM31) :
  Result (core.result.Result (field.QM31 × (Array field.QM31 16#usize) ×
    (Array field.QM31 10#usize) × field.QM31 × field.QM31 × field.QM31)
    pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  := do
  let b ←
    core.option.Option.is_some_and
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnOnceTupleU32Bool
      public1.withdrawal_amount ()
  if b
  then
    ok (core.result.Result.Err
      pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidPublicAmount)
  else
    let r ← pool_v1.pair_forest_semantic_terminal.validate_transition public1
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let a ←
        array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
          pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
          field.QM31.ZERO claims
      let a1 ←
        array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
          pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
          field.QM31.ZERO claims
      let a2 ←
        array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
          pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
          field.QM31.ZERO claims
      let mask_only ←
        array_from_fn_copy 10#usize field.QM31.Insts.CoreMarkerCopy
          pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
          field.QM31.ZERO claims
      let selectors ←
        pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point
      let sops ←
        pool_v1.pair_forest_semantic_terminal.poseidon_selectors selectors
      let poseidon ←
        state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
          { z := a, succ_z := a1, xor12_z := a2 } sops
      let semantic ←
        pool_v1.pair_forest_semantic_terminal.semantic_packed public1
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
      let s ← lift (Array.to_slice semantic)
      let i1 := Slice.len s
      let iter ←
        core.iter.traits.iterator.Iterator.rev.trait_default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize) { start := 0#usize, «end» := i1 }
      let composition ←
        pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 iter
          semantic prepared_theta copy.residual
      let s1 ← lift (Array.to_slice poseidon)
      let i2 := Slice.len s1
      let iter1 ←
        core.iter.traits.iterator.Iterator.rev.trait_default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize) { start := 0#usize, «end» := i2 }
      let composition1 ←
        pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 iter1
          poseidon prepared_theta composition
      let i3 ← pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN
      let q ←
        pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize i3
      ok (core.result.Result.Ok (composition1, a, mask_only, q, h1_z,
        copy.active))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (field.QM31 × (Array field.QM31 16#usize) × (Array field.QM31
        10#usize) × field.QM31 × field.QM31 × field.QM31)
        (core.convert.FromSame
        pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
        residual
