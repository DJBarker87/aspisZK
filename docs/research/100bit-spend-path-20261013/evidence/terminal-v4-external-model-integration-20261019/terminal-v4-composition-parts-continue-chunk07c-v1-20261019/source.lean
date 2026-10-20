import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CompositionGatherClosuresChunk07aV2
import TerminalV4CompositionSelectorSupportChunk07bV1
import TerminalV4ValidateTransitionPredecessorV4
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe
abbrev TerminalOutput := field.QM31 × (Array field.QM31 16#usize) ×
  (Array field.QM31 10#usize) × field.QM31 × field.QM31 × field.QM31
abbrev PoseidonEvaluator := state_only_poseidon.StateOnlyPoseidonOpenings →
  state_only_poseidon.StateOnlyPoseidonSelectors → Result (Array field.QM31 4#usize)
abbrev SemanticEvaluator := pool_v1.pair_forest_semantic_terminal.SemanticPublic →
  state_only_poseidon.StateOnlyPoseidonOpenings →
  pool_v1.pair_forest_copy_terminal.Selectors → Result (Array field.QM31 24#usize)
/-- Current generated `composition_parts` continue branch, after the source
validation `ControlFlow.Continue` cut. The exact closure gathers, selector
construction, copy evaluator, multiplier setup, and reverse composition folds
are retained. The two computations whose source cones are compiled separately
are explicit call parameters. -/
def composition_parts_continue
  (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (o : Option Std.U32) (claims : Array field.QM31 84#usize)
  (point : Array field.QM31 10#usize) (lambda chi theta : field.QM31) :
  Result (core.result.Result TerminalOutput
    pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  := do
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
        poseidonEval { z := a, succ_z := a1, xor12_z := a2 } sops
      let semantic ←
        semanticEval
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
end AspisR1SelectedMaskProbe
