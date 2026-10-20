-- Exact current generated `composition_parts` body, isolated after its
-- generated copy evaluator and composition fold predecessors.
import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CompositionGatherClosuresChunk07aV2
import TerminalV4ValidateTransitionPredecessorV4
import TerminalV4CompositionPartsContinueChunk07cV1
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
def pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
  (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
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
      let b : Bool ←
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
      composition_parts_continue
        poseidonEval semanticEval public1 o claims point lambda chi theta
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (field.QM31 × (Array field.QM31 16#usize) × (Array field.QM31
        10#usize) × field.QM31 × field.QM31 × field.QM31)
        (core.convert.FromSame
        pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
        residual

end AspisR1SelectedMaskProbe
