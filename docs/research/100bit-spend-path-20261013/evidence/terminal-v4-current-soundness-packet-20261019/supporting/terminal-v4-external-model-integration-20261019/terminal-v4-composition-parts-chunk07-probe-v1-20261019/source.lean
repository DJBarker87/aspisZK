-- Exact current generated `composition_parts` body, isolated after its
-- generated copy evaluator and composition fold predecessors.
import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CompositionLoopsChunk06V5
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe
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
             ok (amount >= i)
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

end AspisR1SelectedMaskProbe
